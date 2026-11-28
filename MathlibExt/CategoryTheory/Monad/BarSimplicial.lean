/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Monad.Bar
public import MathlibExt.AlgebraicTopology.SimplicialObject.ToSimplicial

/-!
# Two-sided bar: simplicial assembly

Mathematical source: J. P. May, *The Geometry of Iterated Loop Spaces*,
Lecture Notes in Mathematics 271, Springer, 1972, Chapter 9,
Construction 9.6 and Remark 9.12, <https://doi.org/10.1007/BFb0067491>.

May's functor-valued two-sided bar has degree `n` of the form `Y C^n X`;
here `B(R,T,L)_n = R(T^n(L(-)))`, written in Lean's diagrammatic functor
order as `L.functor ⋙ monadPow T n ⋙ R.functor`. This API publicly counts
faces from the right-module end (`d₀` is the right action and `d_{n+1}`
the left action), while the internal `muAtPos`/`etaAtPos` count from the
left-module end and `barMuAtPos`/`barEtaAtPos` apply `Fin.rev`.

This module assembles the already-proved bar operators into
`SimplicialObject.Data` (`barData`) and the genuine two-sided bar (`twoSidedBar`).

This module does not reprove monad/module calculus and adds no
augmentations or contractions.
-/

@[expose] public section

namespace CategoryTheory
namespace Monad

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type u₃} [Category.{v₃} A]

section FinRevLemmas

/--
Index conversion: `Fin.castSucc` commutes with `Fin.rev` up to `Fin.succ`,
transporting public right-counted bar indices to raw left-counted positions.
-/
theorem fin_rev_castSucc {n : ℕ} (i : Fin n) :
    (Fin.castSucc i : Fin (n + 1)).rev = (i.rev).succ :=
  Fin.rev_castSucc i

theorem fin_rev_succ {n : ℕ} (i : Fin n) :
    (Fin.succ i : Fin (n + 1)).rev = (i.rev).castSucc :=
  Fin.rev_succ i

theorem fin_rev_le_iff {n : ℕ} {i j : Fin n} : j.rev ≤ i.rev ↔ i ≤ j := by
  rw [Fin.rev_le_rev]

end FinRevLemmas

section BarFaceHelpers

variable {T : Monad C} {R : RightModule T D} {L : LeftModule A T}

/--
Right endpoint: face index `0` (`d₀`) is the iterated right action
`rightActionPow`.
-/
lemma barFaceApp_of_val_zero {n : ℕ} {a : A} {i : Fin (n + 2)} (hi : i.val = 0) :
    barFaceApp (T := T) (R := R) (L := L) n i a = rightActionPow T R n (L.functor.obj a) := by
  unfold barFaceApp
  rw [dite_eq_left hi]

/-- Left endpoint: face index `n + 1` (`d_{n+1}`) is the mapped left action. -/
lemma barFaceApp_of_val_last {n : ℕ} {a : A} {i : Fin (n + 2)} (hi : i.val = n + 1) :
    barFaceApp (T := T) (R := R) (L := L) n i a =
      R.functor.map ((monadPow T n).map (L.action.app a)) := by
  have h0 : ¬ (i.val = 0) := by omega
  unfold barFaceApp
  rw [dite_eq_right h0, dite_eq_left hi]

/--
Interior faces: index `i.val = k.val + 1` acts by mapped `barMuAtPos`
(that is, `muAtPos` at the reversed index `k.rev`).
-/
lemma barFaceApp_of_middle {n : ℕ} {a : A} {i : Fin (n + 2)} {k : Fin n}
    (hk : i.val = k.val + 1) :
    barFaceApp (T := T) (R := R) (L := L) n i a =
      R.functor.map (barMuAtPos T n k (L.functor.obj a)) := by
  have h_eq : i = ⟨k.val + 1, by omega⟩ := by
    apply Fin.ext
    simp [hk]
  rw [h_eq]
  exact barFaceApp_middle (T := T) (R := R) (L := L) n k a

end BarFaceHelpers

section FaceFace

variable {T : Monad C} {R : RightModule T D} {L : LeftModule A T}

theorem barFaceApp_face_face (n : ℕ) (i j : Fin (n + 2)) (hij : i ≤ j) (a : A) :
    barFaceApp (T := T) (R := R) (L := L) (n + 1) j.succ a ≫
      barFaceApp (T := T) (R := R) (L := L) n i a =
    barFaceApp (T := T) (R := R) (L := L) (n + 1) i.castSucc a ≫
      barFaceApp (T := T) (R := R) (L := L) n j a := by
  have hij_val : i.val ≤ j.val := (Fin.le_def.mp hij)
  by_cases hi0 : i.val = 0
  · have h_i_right : barFaceApp (T := T) (R := R) (L := L) n i a =
        rightActionPow T R n (L.functor.obj a) :=
      barFaceApp_of_val_zero (T := T) (R := R) (L := L) hi0
    have h_i_cast_val : (Fin.castSucc i : Fin (n + 3)).val = i.val := rfl
    have h_i_cast_zero : (Fin.castSucc i : Fin (n + 3)).val = 0 := by
      rw [h_i_cast_val, hi0]
    have h_i_cast_right : barFaceApp (T := T) (R := R) (L := L) (n + 1) i.castSucc a =
        rightActionPow T R (n + 1) (L.functor.obj a) :=
      barFaceApp_of_val_zero (T := T) (R := R) (L := L) h_i_cast_zero
    by_cases hj0 : j.val = 0
    · have h_j_right : barFaceApp (T := T) (R := R) (L := L) n j a =
          rightActionPow T R n (L.functor.obj a) :=
        barFaceApp_of_val_zero (T := T) (R := R) (L := L) hj0
      have h_j_succ_val : (Fin.succ j : Fin (n + 3)).val = j.val + 1 := rfl
      have h_jsucc_eq : (Fin.succ j : Fin (n + 3)).val =
          (⟨0, by omega⟩ : Fin (n + 1)).val + 1 := by
        rw [h_j_succ_val, hj0]
      have h_jsucc_mid : barFaceApp (T := T) (R := R) (L := L) (n + 1) j.succ a =
          R.functor.map (barMuAtPos T (n + 1) ⟨0, by omega⟩ (L.functor.obj a)) :=
        barFaceApp_of_middle (T := T) (R := R) (L := L) (k := ⟨0, by omega⟩) h_jsucc_eq
      rw [h_jsucc_mid, h_i_right, h_i_cast_right, h_j_right]
      have h_bar : barMuAtPos T (n + 1) ⟨0, by omega⟩ (L.functor.obj a) =
          muAtPos T (n + 1) ⟨n, by omega⟩ (L.functor.obj a) := by
        simp only [barMuAtPos]
        have : (⟨0, by omega⟩ : Fin (n + 1)).rev = ⟨n, by omega⟩ := by
          apply Fin.ext
          simp [Fin.rev]
        rw [this]
      rw [h_bar]
      exact (rightActionPow_assoc_last (T := T) (R := R) (n := n) (X := L.functor.obj a)).symm
    · by_cases hjLast : j.val = n + 1
      · have h_j_left : barFaceApp (T := T) (R := R) (L := L) n j a =
            R.functor.map ((monadPow T n).map (L.action.app a)) :=
          barFaceApp_of_val_last (T := T) (R := R) (L := L) hjLast
        have h_j_succ_val : (Fin.succ j : Fin (n + 3)).val = j.val + 1 := rfl
        have h_jsucc_last : (Fin.succ j : Fin (n + 3)).val = (n + 1) + 1 := by
          rw [h_j_succ_val, hjLast]
        have h_jsucc_left : barFaceApp (T := T) (R := R) (L := L) (n + 1) j.succ a =
            R.functor.map ((monadPow T (n + 1)).map (L.action.app a)) :=
          barFaceApp_of_val_last (T := T) (R := R) (L := L) h_jsucc_last
        rw [h_jsucc_left, h_i_right, h_i_cast_right, h_j_left]
        exact rightActionPow_leftAction T R L n a
      · have hj_pos : 0 < j.val := by omega
        have hj_le : j.val ≤ n := by omega
        have hn_pos : 0 < n := by omega
        let j0 : Fin n := ⟨j.val - 1, by omega⟩
        have hj_eq : j.val = j0.val + 1 := by
          have h1 : 1 ≤ j.val := by omega
          have h2 : j.val - 1 + 1 = j.val := Nat.sub_add_cancel h1
          have hjv : j0.val = j.val - 1 := rfl
          rw [← hjv] at h2
          exact h2.symm
        let kUpper : Fin (n + 1) := ⟨j.val, by omega⟩
        have h_j_right_mid : barFaceApp (T := T) (R := R) (L := L) n j a =
            R.functor.map (barMuAtPos T n j0 (L.functor.obj a)) :=
          barFaceApp_of_middle (T := T) (R := R) (L := L) (k := j0) (by rw [hj_eq])
        have h_j_succ_val : (Fin.succ j : Fin (n + 3)).val = j.val + 1 := rfl
        have h_jsucc_eq : (Fin.succ j : Fin (n + 3)).val = kUpper.val + 1 := by
          have : kUpper.val = j.val := rfl
          rw [h_j_succ_val, this]
        have h_jsucc_mid : barFaceApp (T := T) (R := R) (L := L) (n + 1) j.succ a =
            R.functor.map (barMuAtPos T (n + 1) kUpper (L.functor.obj a)) :=
          barFaceApp_of_middle (T := T) (R := R) (L := L) (k := kUpper) h_jsucc_eq
        have h_j0_succ_eq : kUpper = j0.succ := by
          apply Fin.ext
          have hk : kUpper.val = j.val := rfl
          have hs : j0.succ.val = j0.val + 1 := rfl
          rw [hk, hs, hj_eq]
        rw [h_j0_succ_eq] at h_jsucc_mid
        rw [h_jsucc_mid, h_i_right, h_i_cast_right, h_j_right_mid]
        have h_raw_j0 : barMuAtPos T n j0 (L.functor.obj a) =
            muAtPos T n j0.rev (L.functor.obj a) := rfl
        have h_raw_succ : barMuAtPos T (n + 1) j0.succ (L.functor.obj a) =
            muAtPos T (n + 1) j0.succ.rev (L.functor.obj a) := rfl
        have h_rev : j0.succ.rev = (j0.rev).castSucc := fin_rev_succ j0
        rw [h_raw_j0, h_raw_succ, h_rev]
        exact rightActionPow_mu_castSucc T R n j0.rev (L.functor.obj a)
  · by_cases hiLast : i.val = n + 1
    · have hjLast : j.val = n + 1 := by omega
      have h_i_left : barFaceApp (T := T) (R := R) (L := L) n i a =
          R.functor.map ((monadPow T n).map (L.action.app a)) :=
        barFaceApp_of_val_last (T := T) (R := R) (L := L) hiLast
      have h_j_left : barFaceApp (T := T) (R := R) (L := L) n j a =
          R.functor.map ((monadPow T n).map (L.action.app a)) :=
        barFaceApp_of_val_last (T := T) (R := R) (L := L) hjLast
      have h_i_cast_val : (Fin.castSucc i : Fin (n + 3)).val = i.val := rfl
      have h_j_succ_val : (Fin.succ j : Fin (n + 3)).val = j.val + 1 := rfl
      have h_i_cast_eq : (Fin.castSucc i : Fin (n + 3)).val =
          (⟨n, by omega⟩ : Fin (n + 1)).val + 1 := by
        rw [h_i_cast_val, hiLast]
      have h_jsucc_last : (Fin.succ j : Fin (n + 3)).val = (n + 1) + 1 := by
        rw [h_j_succ_val, hjLast]
      have h_i_cast_mid : barFaceApp (T := T) (R := R) (L := L) (n + 1) i.castSucc a =
          R.functor.map (barMuAtPos T (n + 1) ⟨n, by omega⟩ (L.functor.obj a)) := by
        exact barFaceApp_of_middle (T := T) (R := R) (L := L) (k := ⟨n, by omega⟩) h_i_cast_eq
      have h_jsucc_left : barFaceApp (T := T) (R := R) (L := L) (n + 1) j.succ a =
          R.functor.map ((monadPow T (n + 1)).map (L.action.app a)) := by
        exact barFaceApp_of_val_last (T := T) (R := R) (L := L) h_jsucc_last
      have h_bar : barMuAtPos T (n + 1) ⟨n, by omega⟩ (L.functor.obj a) =
          muAtPos T (n + 1) ⟨0, by omega⟩ (L.functor.obj a) := by
        simp only [barMuAtPos]
        have : (⟨n, by omega⟩ : Fin (n + 1)).rev = ⟨0, by omega⟩ := by
          apply Fin.ext
          simp [Fin.rev]
        rw [this]
      calc barFaceApp (T := T) (R := R) (L := L) (n + 1) j.succ a ≫
              barFaceApp (T := T) (R := R) (L := L) n i a
          = R.functor.map ((monadPow T (n + 1)).map (L.action.app a)) ≫
            R.functor.map ((monadPow T n).map (L.action.app a)) := by
            rw [h_jsucc_left, h_i_left]
        _ = R.functor.map (muAtPos T (n + 1) ⟨0, by omega⟩ (L.functor.obj a)) ≫
            R.functor.map ((monadPow T n).map (L.action.app a)) := by
            rw [leftAction_assoc_zero]
        _ = R.functor.map (barMuAtPos T (n + 1) ⟨n, by omega⟩ (L.functor.obj a)) ≫
            R.functor.map ((monadPow T n).map (L.action.app a)) := by
            rw [h_bar]
        _ = barFaceApp (T := T) (R := R) (L := L) (n + 1) i.castSucc a ≫
              barFaceApp (T := T) (R := R) (L := L) n j a := by
            rw [h_i_cast_mid, h_j_left]
    · have hi_pos : 0 < i.val := by omega
      have hi_le : i.val ≤ n := by omega
      have hn_pos : 0 < n := by omega
      by_cases hjLast : j.val = n + 1
      · let i0 : Fin n := ⟨i.val - 1, by omega⟩
        have hi_eq : i.val = i0.val + 1 := by
          have h1 : 1 ≤ i.val := by omega
          have h2 : i.val - 1 + 1 = i.val := Nat.sub_add_cancel h1
          have hi0v : i0.val = i.val - 1 := rfl
          rw [← hi0v] at h2
          exact h2.symm
        have h_i_mid : barFaceApp (T := T) (R := R) (L := L) n i a =
            R.functor.map (barMuAtPos T n i0 (L.functor.obj a)) :=
          barFaceApp_of_middle (T := T) (R := R) (L := L) (k := i0) (by rw [hi_eq])
        have h_j_left : barFaceApp (T := T) (R := R) (L := L) n j a =
            R.functor.map ((monadPow T n).map (L.action.app a)) :=
          barFaceApp_of_val_last (T := T) (R := R) (L := L) hjLast
        have h_j_succ_val : (Fin.succ j : Fin (n + 3)).val = j.val + 1 := rfl
        have h_jsucc_last : (Fin.succ j : Fin (n + 3)).val = (n + 1) + 1 := by
          rw [h_j_succ_val, hjLast]
        have h_jsucc_left : barFaceApp (T := T) (R := R) (L := L) (n + 1) j.succ a =
            R.functor.map ((monadPow T (n + 1)).map (L.action.app a)) :=
          barFaceApp_of_val_last (T := T) (R := R) (L := L) h_jsucc_last
        have h_i_cast_val : (Fin.castSucc i : Fin (n + 3)).val = i.val := rfl
        let i0c : Fin (n + 1) := i0.castSucc
        have hi0c_val : i0c.val = i0.val := rfl
        have h_i_cast_eq : (Fin.castSucc i : Fin (n + 3)).val = i0c.val + 1 := by
          rw [h_i_cast_val, hi0c_val, hi_eq]
        have h_i_cast_mid : barFaceApp (T := T) (R := R) (L := L) (n + 1) i.castSucc a =
            R.functor.map (barMuAtPos T (n + 1) i0c (L.functor.obj a)) := by
          exact barFaceApp_of_middle (T := T) (R := R) (L := L) (k := i0c) h_i_cast_eq
        rw [h_jsucc_left, h_i_mid, h_i_cast_mid, h_j_left]
        have h_raw_i0 : barMuAtPos T n i0 (L.functor.obj a) =
            muAtPos T n i0.rev (L.functor.obj a) := rfl
        have h_raw_i0c : barMuAtPos T (n + 1) i0c (L.functor.obj a) =
            muAtPos T (n + 1) i0c.rev (L.functor.obj a) := rfl
        have h_rev : i0c.rev = (i0.rev).succ := fin_rev_castSucc i0
        rw [h_raw_i0, h_raw_i0c, h_rev]
        exact (leftAction_mu_succ (T := T) (R := R) (L := L) n i0.rev a).symm
      · have hj_pos : 0 < j.val := by omega
        have hj_le : j.val ≤ n := by omega
        let i0 : Fin n := ⟨i.val - 1, by omega⟩
        let j0 : Fin n := ⟨j.val - 1, by omega⟩
        have hi_eq : i.val = i0.val + 1 := by
          have h1 : 1 ≤ i.val := by omega
          have h2 : i.val - 1 + 1 = i.val := Nat.sub_add_cancel h1
          have hi0v : i0.val = i.val - 1 := rfl
          rw [← hi0v] at h2
          exact h2.symm
        have hj_eq : j.val = j0.val + 1 := by
          have h1 : 1 ≤ j.val := by omega
          have h2 : j.val - 1 + 1 = j.val := Nat.sub_add_cancel h1
          have hj0v : j0.val = j.val - 1 := rfl
          rw [← hj0v] at h2
          exact h2.symm
        have hi_le_j0 : i0 ≤ j0 := by
          have hle : i0.val + 1 ≤ j0.val + 1 := by
            rw [← hi_eq, ← hj_eq]
            exact hij_val
          have : i0.val ≤ j0.val := by omega
          exact (Fin.le_def.mpr this)
        have h_i_mid : barFaceApp (T := T) (R := R) (L := L) n i a =
            R.functor.map (barMuAtPos T n i0 (L.functor.obj a)) :=
          barFaceApp_of_middle (T := T) (R := R) (L := L) (k := i0) (by rw [hi_eq])
        have h_j_mid : barFaceApp (T := T) (R := R) (L := L) n j a =
            R.functor.map (barMuAtPos T n j0 (L.functor.obj a)) :=
          barFaceApp_of_middle (T := T) (R := R) (L := L) (k := j0) (by rw [hj_eq])
        have h_i_cast_val : (Fin.castSucc i : Fin (n + 3)).val = i.val := rfl
        have h_j_succ_val : (Fin.succ j : Fin (n + 3)).val = j.val + 1 := rfl
        let i0c : Fin (n + 1) := i0.castSucc
        let j0s : Fin (n + 1) := j0.succ
        have hi0c_val : i0c.val = i0.val := rfl
        have hj0s_val : j0s.val = j0.val + 1 := rfl
        have h_i_cast_eq : (Fin.castSucc i : Fin (n + 3)).val = i0c.val + 1 := by
          rw [h_i_cast_val, hi0c_val, hi_eq]
        have h_j_succ_eq : (Fin.succ j : Fin (n + 3)).val = j0s.val + 1 := by
          rw [h_j_succ_val, hj0s_val, hj_eq]
        have h_i_cast_mid : barFaceApp (T := T) (R := R) (L := L) (n + 1) i.castSucc a =
            R.functor.map (barMuAtPos T (n + 1) i0c (L.functor.obj a)) :=
          barFaceApp_of_middle (T := T) (R := R) (L := L) (k := i0c) h_i_cast_eq
        have h_j_succ_mid : barFaceApp (T := T) (R := R) (L := L) (n + 1) j.succ a =
            R.functor.map (barMuAtPos T (n + 1) j0s (L.functor.obj a)) :=
          barFaceApp_of_middle (T := T) (R := R) (L := L) (k := j0s) h_j_succ_eq
        rw [h_j_succ_mid, h_i_mid, h_i_cast_mid, h_j_mid]
        have h_raw_i0 : barMuAtPos T n i0 (L.functor.obj a) =
            muAtPos T n i0.rev (L.functor.obj a) := rfl
        have h_raw_j0 : barMuAtPos T n j0 (L.functor.obj a) =
            muAtPos T n j0.rev (L.functor.obj a) := rfl
        have h_raw_i0c : barMuAtPos T (n + 1) i0c (L.functor.obj a) =
            muAtPos T (n + 1) i0c.rev (L.functor.obj a) := rfl
        have h_raw_j0s : barMuAtPos T (n + 1) j0s (L.functor.obj a) =
            muAtPos T (n + 1) j0s.rev (L.functor.obj a) := rfl
        have h_rc : i0c.rev = (i0.rev).succ := fin_rev_castSucc i0
        have h_rs : j0s.rev = (j0.rev).castSucc := fin_rev_succ j0
        rw [h_raw_i0, h_raw_j0, h_raw_i0c, h_raw_j0s, h_rc, h_rs]
        have h_le_rev : j0.rev ≤ i0.rev := by
          rwa [fin_rev_le_iff]
        have h_mu := muAtPos_face_face (T := T) n j0.rev i0.rev h_le_rev (L.functor.obj a)
        calc R.functor.map (muAtPos T (n + 1) (j0.rev).castSucc (L.functor.obj a)) ≫
                R.functor.map (muAtPos T n i0.rev (L.functor.obj a))
            = R.functor.map (muAtPos T (n + 1) (j0.rev).castSucc (L.functor.obj a) ≫
                  muAtPos T n i0.rev (L.functor.obj a)) := by
              rw [← R.functor.map_comp]
          _ = R.functor.map (muAtPos T (n + 1) (i0.rev).succ (L.functor.obj a) ≫
                  muAtPos T n j0.rev (L.functor.obj a)) := by
              rw [h_mu]
          _ = R.functor.map (muAtPos T (n + 1) (i0.rev).succ (L.functor.obj a)) ≫
                  R.functor.map (muAtPos T n j0.rev (L.functor.obj a)) := by
              rw [R.functor.map_comp]

theorem barFace_face (n : ℕ) (i j : Fin (n + 2)) (hij : i ≤ j) :
    barFace (T := T) (R := R) (L := L) (n + 1) j.succ ≫ barFace n i =
    barFace (T := T) (R := R) (L := L) (n + 1) i.castSucc ≫ barFace n j := by
  ext a : 2
  exact barFaceApp_face_face (T := T) (R := R) (L := L) n i j hij a

end FaceFace

section DegDeg

variable {T : Monad C} {R : RightModule T D} {L : LeftModule A T}

theorem barDegeneracyApp_sigma_sigma (n : ℕ) (i j : Fin (n + 1)) (hij : i ≤ j) (a : A) :
    (barDegeneracy (T := T) (R := R) (L := L) n j).app a ≫
      (barDegeneracy (T := T) (R := R) (L := L) (n + 1) i.castSucc).app a =
    (barDegeneracy (T := T) (R := R) (L := L) n i).app a ≫
      (barDegeneracy (T := T) (R := R) (L := L) (n + 1) j.succ).app a := by
  let X := L.functor.obj a
  have h_left_map :
      (barDegeneracy (T := T) (R := R) (L := L) n j).app a ≫
        (barDegeneracy (T := T) (R := R) (L := L) (n + 1) i.castSucc).app a =
      R.functor.map (barEtaAtPos T n j X ≫ barEtaAtPos T (n + 1) i.castSucc X) := by
    simp only [barDegeneracy]
    rw [← R.functor.map_comp]
  have h_right_map :
      (barDegeneracy (T := T) (R := R) (L := L) n i).app a ≫
        (barDegeneracy (T := T) (R := R) (L := L) (n + 1) j.succ).app a =
      R.functor.map (barEtaAtPos T n i X ≫ barEtaAtPos T (n + 1) j.succ X) := by
    simp only [barDegeneracy]
    rw [← R.functor.map_comp]
  rw [h_left_map, h_right_map]
  have hr1 : (Fin.castSucc i : Fin (n + 2)).rev = i.rev.succ := fin_rev_castSucc i
  have hr2 : (Fin.succ j : Fin (n + 2)).rev = j.rev.castSucc := fin_rev_succ j
  have h_inner :
      barEtaAtPos T n j X ≫ barEtaAtPos T (n + 1) i.castSucc X =
      barEtaAtPos T n i X ≫ barEtaAtPos T (n + 1) j.succ X := by
    calc
      barEtaAtPos T n j X ≫ barEtaAtPos T (n + 1) i.castSucc X
          = etaAtPos T n j.rev X ≫ etaAtPos T (n + 1) (i.castSucc).rev X := rfl
      _ = etaAtPos T n j.rev X ≫ etaAtPos T (n + 1) (i.rev.succ) X := by rw [hr1]
      _ = etaAtPos T n i.rev X ≫ etaAtPos T (n + 1) (j.rev.castSucc) X := by
            have hle : j.rev ≤ i.rev := by
              rwa [fin_rev_le_iff]
            have heq := etaAtPos_deg_deg (T := T) n j.rev i.rev hle X
            exact heq.symm
      _ = etaAtPos T n i.rev X ≫ etaAtPos T (n + 1) (j.succ).rev X := by rw [← hr2]
      _ = barEtaAtPos T n i X ≫ barEtaAtPos T (n + 1) j.succ X := rfl
  rw [h_inner]

theorem barDegeneracy_sigma_sigma (n : ℕ) (i j : Fin (n + 1)) (hij : i ≤ j) :
    barDegeneracy (T := T) (R := R) (L := L) n j ≫
      barDegeneracy (T := T) (R := R) (L := L) (n + 1) i.castSucc =
    barDegeneracy (T := T) (R := R) (L := L) n i ≫
      barDegeneracy (T := T) (R := R) (L := L) (n + 1) j.succ := by
  ext a : 2
  exact barDegeneracyApp_sigma_sigma n i j hij a

end DegDeg

section DegFaceSelf

variable {T : Monad C} {R : RightModule T D} {L : LeftModule A T}

theorem barDegeneracyApp_self (n : ℕ) (i : Fin (n + 1)) (a : A) :
    (barDegeneracy (T := T) (R := R) (L := L) n i).app a ≫
      barFaceApp (T := T) (R := R) (L := L) n i.castSucc a =
    𝟙 _ := by
  let X := L.functor.obj a
  by_cases h0 : i.val = 0
  · have hi_cast_val : (Fin.castSucc i : Fin (n + 2)).val = 0 := by
      simp [Fin.castSucc, h0]
    have h_face : barFaceApp (T := T) (R := R) (L := L) n (Fin.castSucc i) a =
        rightActionPow T R n X :=
      barFaceApp_of_val_zero (T := T) (R := R) (L := L) hi_cast_val
    have h_rev : i.rev = ⟨n, by omega⟩ := by
      apply Fin.ext
      simp [Fin.rev, h0]
    have h_deg : (barDegeneracy (T := T) (R := R) (L := L) n i).app a =
        R.functor.map (etaAtPos T n ⟨n, by omega⟩ (L.functor.obj a)) := by
      simp only [barDegeneracy, barEtaAtPos, h_rev]
    rw [h_face, h_deg]
    have hX : (L.functor.obj a) = X := rfl
    rw [hX] at *
    exact rightActionPow_unit_last T R n X
  · have hi_pos : 0 < i.val := by omega
    have hn : 0 < n := by omega
    let k : Fin n := ⟨i.val - 1, by omega⟩
    have hi_eq : i.val = k.val + 1 := by
      have hk : k.val = i.val - 1 := rfl
      omega
    have hi_cast_eq : (Fin.castSucc i : Fin (n + 2)).val = k.val + 1 := by
      simp [Fin.castSucc, hi_eq]
    have h_face : barFaceApp (T := T) (R := R) (L := L) n (Fin.castSucc i) a =
        R.functor.map (barMuAtPos T n k X) :=
      barFaceApp_of_middle (T := T) (R := R) (L := L) (k := k) hi_cast_eq
    have h_rev_eq : i.rev = (k.rev).castSucc := by
      apply Fin.ext
      simp [Fin.rev, k]
      omega
    have h_deg : (barDegeneracy (T := T) (R := R) (L := L) n i).app a =
        R.functor.map (etaAtPos T n (k.rev.castSucc) X) := by
      simp only [barDegeneracy, barEtaAtPos]
      rw [h_rev_eq]
    have h_mu : barMuAtPos T n k X = muAtPos T n k.rev X := rfl
    rw [h_face, h_deg, h_mu]
    calc
      R.functor.map (etaAtPos T n (k.rev.castSucc) X) ≫
          R.functor.map (muAtPos T n k.rev X)
          = R.functor.map (etaAtPos T n (k.rev.castSucc) X ≫ muAtPos T n k.rev X) := by
            rw [← R.functor.map_comp]
      _ = R.functor.map (𝟙 _) := by rw [etaAtPos_castSucc_muAtPos]
      _ = 𝟙 _ := by rw [R.functor.map_id]

theorem barDegeneracy_self (n : ℕ) (i : Fin (n + 1)) :
    barDegeneracy (T := T) (R := R) (L := L) n i ≫
      barFace (T := T) (R := R) (L := L) n i.castSucc =
    𝟙 (barObj T R L n) := by
  ext a : 2
  exact barDegeneracyApp_self n i a

end DegFaceSelf

section DegFaceSucc

variable {T : Monad C} {R : RightModule T D} {L : LeftModule A T}

theorem barDegeneracyApp_succ (n : ℕ) (i : Fin (n + 1)) (a : A) :
    (barDegeneracy (T := T) (R := R) (L := L) n i).app a ≫
      barFaceApp (T := T) (R := R) (L := L) n i.succ a =
    𝟙 _ := by
  let X := L.functor.obj a
  by_cases h_last : i.val = n
  · have hi_succ_val : (Fin.succ i : Fin (n + 2)).val = n + 1 := by
      simp [Fin.succ, h_last]
    have h_face : barFaceApp (T := T) (R := R) (L := L) n (Fin.succ i) a =
        R.functor.map ((monadPow T n).map (L.action.app a)) :=
      barFaceApp_of_val_last (T := T) (R := R) (L := L) hi_succ_val
    have h_rev : i.rev = ⟨0, by omega⟩ := by
      apply Fin.ext
      simp [Fin.rev, h_last]
    have h_deg : (barDegeneracy (T := T) (R := R) (L := L) n i).app a =
        R.functor.map (etaAtPos T n ⟨0, by omega⟩ (L.functor.obj a)) := by
      simp only [barDegeneracy, barEtaAtPos, h_rev]
    rw [h_face, h_deg]
    exact leftAction_unit_zero T R L n a
  · have hi_lt : i.val < n := by omega
    let k : Fin n := ⟨i.val, by omega⟩
    have hi_succ_eq : (Fin.succ i : Fin (n + 2)).val = k.val + 1 := by
      simp [Fin.succ, k]
    have h_face : barFaceApp (T := T) (R := R) (L := L) n (Fin.succ i) a =
        R.functor.map (barMuAtPos T n k X) :=
      barFaceApp_of_middle (T := T) (R := R) (L := L) (k := k) hi_succ_eq
    have h_rev_eq : i.rev = (k.rev).succ := by
      apply Fin.ext
      simp [Fin.rev, k]
      omega
    have h_deg : (barDegeneracy (T := T) (R := R) (L := L) n i).app a =
        R.functor.map (etaAtPos T n (k.rev.succ) X) := by
      simp only [barDegeneracy, barEtaAtPos]
      rw [h_rev_eq]
    have h_mu : barMuAtPos T n k X = muAtPos T n k.rev X := rfl
    rw [h_face, h_deg, h_mu]
    calc
      R.functor.map (etaAtPos T n (k.rev.succ) X) ≫
          R.functor.map (muAtPos T n k.rev X)
          = R.functor.map (etaAtPos T n (k.rev.succ) X ≫ muAtPos T n k.rev X) := by
            rw [← R.functor.map_comp]
      _ = R.functor.map (𝟙 _) := by rw [etaAtPos_succ_muAtPos]
      _ = 𝟙 _ := by rw [R.functor.map_id]

theorem barDegeneracy_succ (n : ℕ) (i : Fin (n + 1)) :
    barDegeneracy (T := T) (R := R) (L := L) n i ≫
      barFace (T := T) (R := R) (L := L) n i.succ =
    𝟙 (barObj T R L n) := by
  ext a : 2
  exact barDegeneracyApp_succ n i a

end DegFaceSucc

section DegFaceOfLe

variable {T : Monad C} {R : RightModule T D} {L : LeftModule A T}

theorem barDegeneracyApp_of_le {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : i ≤ j.castSucc) (a : A) :
    (barDegeneracy (T := T) (R := R) (L := L) (n + 1) j.succ).app a ≫
      barFaceApp (T := T) (R := R) (L := L) (n + 1) i.castSucc a =
    barFaceApp (T := T) (R := R) (L := L) n i a ≫
      (barDegeneracy (T := T) (R := R) (L := L) n j).app a := by
  let X := L.functor.obj a
  have h_val : i.val ≤ j.val := by
    have := Fin.le_def.mp h
    simpa using this
  by_cases hi0 : i.val = 0
  · have h_face_n : barFaceApp (T := T) (R := R) (L := L) n i a =
        rightActionPow T R n X :=
      barFaceApp_of_val_zero (T := T) (R := R) (L := L) hi0
    have h_cast_zero : (Fin.castSucc i : Fin (n + 3)).val = 0 := by
      simp [hi0]
    have h_face_Sn : barFaceApp (T := T) (R := R) (L := L) (n + 1) i.castSucc a =
        rightActionPow T R (n + 1) X :=
      barFaceApp_of_val_zero (T := T) (R := R) (L := L) h_cast_zero
    have h_rev_succ : (j.succ : Fin (n + 2)).rev = j.rev.castSucc :=
      fin_rev_succ j
    have h_eta_Sn : barEtaAtPos T (n + 1) j.succ X =
        etaAtPos T (n + 1) j.rev.castSucc X := by
      simp only [barEtaAtPos, h_rev_succ]
    have h_eta_n : barEtaAtPos T n j X = etaAtPos T n j.rev X := rfl
    calc (barDegeneracy (T := T) (R := R) (L := L) (n + 1) j.succ).app a ≫
            barFaceApp (T := T) (R := R) (L := L) (n + 1) i.castSucc a
        = R.functor.map (barEtaAtPos T (n + 1) j.succ X) ≫ rightActionPow T R (n + 1) X := by
          rw [h_face_Sn]
          rfl
      _ = R.functor.map (etaAtPos T (n + 1) j.rev.castSucc X) ≫ rightActionPow T R (n + 1) X := by
          rw [h_eta_Sn]
      _ = rightActionPow T R n X ≫ R.functor.map (etaAtPos T n j.rev X) := by
          exact rightActionPow_eta_castSucc T R n j.rev X
      _ = rightActionPow T R n X ≫ R.functor.map (barEtaAtPos T n j X) := by
          rw [h_eta_n]
      _ = barFaceApp (T := T) (R := R) (L := L) n i a ≫
            (barDegeneracy (T := T) (R := R) (L := L) n j).app a := by
          rw [h_face_n]
          rfl
  · have hi_not_last : i.val ≠ n + 1 := by
      intro h_last
      have : j.val ≤ n := by omega
      omega
    have hi_pos : 0 < i.val := by omega
    have hi_le_n : i.val ≤ n := by omega
    have hk_n : i.val - 1 < n := by omega
    let i0 : Fin n := ⟨i.val - 1, hk_n⟩
    have hi_eq : i.val = i0.val + 1 := by
      have : i0.val = i.val - 1 := rfl
      omega
    have h_face_n : barFaceApp (T := T) (R := R) (L := L) n i a =
        R.functor.map (barMuAtPos T n i0 X) :=
      barFaceApp_of_middle (T := T) (R := R) (L := L) (k := i0) hi_eq
    have hk_Sn : i.val - 1 < n + 1 := by omega
    let i0c : Fin (n + 1) := ⟨i.val - 1, hk_Sn⟩
    have hi0c_eq : i0c = i0.castSucc := by
      apply Fin.ext
      rfl
    have hi0c_val : i0c.val = i0.val := rfl
    have h_cast_eq : (Fin.castSucc i : Fin (n + 3)).val = i0c.val + 1 := by
      have h1 : (Fin.castSucc i).val = i.val := rfl
      have h2 : i.val = i0.val + 1 := hi_eq
      have h3 : i0.val = i0c.val := by rw [hi0c_val]
      omega
    have h_face_Sn : barFaceApp (T := T) (R := R) (L := L) (n + 1) i.castSucc a =
        R.functor.map (barMuAtPos T (n + 1) i0c X) :=
      barFaceApp_of_middle (T := T) (R := R) (L := L) (k := i0c) h_cast_eq
    have h_rev_succ : (j.succ : Fin (n + 2)).rev = j.rev.castSucc :=
      fin_rev_succ j
    have h_eta_Sn : barEtaAtPos T (n + 1) j.succ X =
        etaAtPos T (n + 1) j.rev.castSucc X := by
      simp only [barEtaAtPos, h_rev_succ]
    have h_eta_n : barEtaAtPos T n j X = etaAtPos T n j.rev X := rfl
    have h_mu_n : barMuAtPos T n i0 X = muAtPos T n i0.rev X := rfl
    have h_rev_cast : i0c.rev = i0.rev.succ := by
      rw [hi0c_eq]
      exact fin_rev_castSucc i0
    have h_mu_Sn : barMuAtPos T (n + 1) i0c X = muAtPos T (n + 1) i0.rev.succ X := by
      calc barMuAtPos T (n + 1) i0c X = muAtPos T (n + 1) i0c.rev X := rfl
        _ = muAtPos T (n + 1) i0.rev.succ X := by rw [h_rev_cast]
    have h_le_rev : j.rev.val ≤ i0.rev.val := by
      have hj_rev : j.rev.val = (n + 1) - (j.val + 1) := rfl
      have hi_rev : i0.rev.val = n - (i0.val + 1) := rfl
      omega
    have h_inter := etaAtPos_castSucc_muAtPos_succ_of_le (T := T) n i0.rev j.rev h_le_rev X
    calc (barDegeneracy (T := T) (R := R) (L := L) (n + 1) j.succ).app a ≫
            barFaceApp (T := T) (R := R) (L := L) (n + 1) i.castSucc a
        = R.functor.map (barEtaAtPos T (n + 1) j.succ X) ≫
            R.functor.map (barMuAtPos T (n + 1) i0c X) := by
          rw [h_face_Sn]; rfl
      _ = R.functor.map (etaAtPos T (n + 1) j.rev.castSucc X) ≫
            R.functor.map (muAtPos T (n + 1) i0.rev.succ X) := by
          rw [h_eta_Sn, h_mu_Sn]
      _ = R.functor.map (etaAtPos T (n + 1) j.rev.castSucc X ≫
            muAtPos T (n + 1) i0.rev.succ X) := by
          rw [← R.functor.map_comp]
      _ = R.functor.map (muAtPos T n i0.rev X ≫ etaAtPos T n j.rev X) := by
          rw [h_inter]
      _ = R.functor.map (muAtPos T n i0.rev X) ≫
            R.functor.map (etaAtPos T n j.rev X) := by
          rw [R.functor.map_comp]
      _ = R.functor.map (barMuAtPos T n i0 X) ≫
            R.functor.map (barEtaAtPos T n j X) := by
          rw [h_mu_n, h_eta_n]
      _ = barFaceApp (T := T) (R := R) (L := L) n i a ≫
            (barDegeneracy (T := T) (R := R) (L := L) n j).app a := by
          rw [h_face_n]; rfl

theorem barDegeneracy_of_le {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : i ≤ j.castSucc) :
    barDegeneracy (T := T) (R := R) (L := L) (n + 1) j.succ ≫
      barFace (T := T) (R := R) (L := L) (n + 1) i.castSucc =
    barFace (T := T) (R := R) (L := L) n i ≫
      barDegeneracy (T := T) (R := R) (L := L) n j := by
  ext a : 2
  exact barDegeneracyApp_of_le (T := T) (R := R) (L := L) (j := j) h a

end DegFaceOfLe

section DegFaceOfGt

variable {T : Monad C} {R : RightModule T D} {L : LeftModule A T}

theorem barDegeneracyApp_of_gt {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : j.castSucc < i) (a : A) :
    (barDegeneracy (T := T) (R := R) (L := L) (n + 1) j.castSucc).app a ≫
      barFaceApp (T := T) (R := R) (L := L) (n + 1) i.succ a =
    barFaceApp (T := T) (R := R) (L := L) n i a ≫
      (barDegeneracy (T := T) (R := R) (L := L) n j).app a := by
  let X := L.functor.obj a
  have h_val : j.val < i.val := by
    have := Fin.lt_def.mp h
    simpa using this
  have hi_pos : 0 < i.val := by omega
  by_cases hi_last : i.val = n + 1
  · have h_face_n : barFaceApp (T := T) (R := R) (L := L) n i a =
        R.functor.map ((monadPow T n).map (L.action.app a)) :=
      barFaceApp_of_val_last (T := T) (R := R) (L := L) hi_last
    have h_succ_last : (Fin.succ i : Fin (n + 3)).val = n + 2 := by
      simp [Fin.succ, hi_last]
    have h_face_Sn : barFaceApp (T := T) (R := R) (L := L) (n + 1) i.succ a =
        R.functor.map ((monadPow T (n + 1)).map (L.action.app a)) :=
      barFaceApp_of_val_last (T := T) (R := R) (L := L) h_succ_last
    have h_rev_cast : (Fin.castSucc j : Fin (n + 2)).rev = j.rev.succ :=
      fin_rev_castSucc j
    have h_eta_Sn : barEtaAtPos T (n + 1) j.castSucc X =
        etaAtPos T (n + 1) j.rev.succ X := by
      simp only [barEtaAtPos, h_rev_cast]
    have h_eta_n : barEtaAtPos T n j X = etaAtPos T n j.rev X := rfl
    calc (barDegeneracy (T := T) (R := R) (L := L) (n + 1) j.castSucc).app a ≫
            barFaceApp (T := T) (R := R) (L := L) (n + 1) i.succ a
        = R.functor.map (barEtaAtPos T (n + 1) j.castSucc X) ≫
            R.functor.map ((monadPow T (n + 1)).map (L.action.app a)) := by
          rw [h_face_Sn]; rfl
      _ = R.functor.map (etaAtPos T (n + 1) j.rev.succ X) ≫
            R.functor.map ((monadPow T (n + 1)).map (L.action.app a)) := by
          rw [h_eta_Sn]
      _ = R.functor.map ((monadPow T n).map (L.action.app a)) ≫
            R.functor.map (etaAtPos T n j.rev X) := by
          exact leftAction_eta_succ (T := T) (R := R) (L := L) n j.rev a
      _ = R.functor.map ((monadPow T n).map (L.action.app a)) ≫
            R.functor.map (barEtaAtPos T n j X) := by
          rw [h_eta_n]
      _ = barFaceApp (T := T) (R := R) (L := L) n i a ≫
            (barDegeneracy (T := T) (R := R) (L := L) n j).app a := by
          rw [h_face_n]; rfl
  · have hi_not_last : i.val ≠ n + 1 := hi_last
    have hi_le_n : i.val ≤ n := by omega
    have hk_n : i.val - 1 < n := by omega
    let i0 : Fin n := ⟨i.val - 1, hk_n⟩
    have hi_eq : i.val = i0.val + 1 := by
      have : i0.val = i.val - 1 := rfl
      omega
    have h_face_n : barFaceApp (T := T) (R := R) (L := L) n i a =
        R.functor.map (barMuAtPos T n i0 X) :=
      barFaceApp_of_middle (T := T) (R := R) (L := L) (k := i0) hi_eq
    have hk_Sn1 : i.val < n + 1 := by omega
    let i0s : Fin (n + 1) := ⟨i.val, hk_Sn1⟩
    have hi0s_eq : i0s = i0.succ := by
      apply Fin.ext
      have : i0s.val = i.val := rfl
      have : (i0.succ).val = i0.val + 1 := rfl
      have : i0.val = i.val - 1 := rfl
      omega
    have h_succ_eq : (Fin.succ i : Fin (n + 3)).val = i0s.val + 1 := by
      have : (Fin.succ i).val = i.val + 1 := rfl
      have : i0s.val = i.val := rfl
      omega
    have h_face_Sn : barFaceApp (T := T) (R := R) (L := L) (n + 1) i.succ a =
        R.functor.map (barMuAtPos T (n + 1) i0s X) :=
      barFaceApp_of_middle (T := T) (R := R) (L := L) (k := i0s) h_succ_eq
    have h_rev_cast : (Fin.castSucc j : Fin (n + 2)).rev = j.rev.succ :=
      fin_rev_castSucc j
    have h_eta_Sn : barEtaAtPos T (n + 1) j.castSucc X =
        etaAtPos T (n + 1) j.rev.succ X := by
      simp only [barEtaAtPos, h_rev_cast]
    have h_eta_n : barEtaAtPos T n j X = etaAtPos T n j.rev X := rfl
    have h_mu_n : barMuAtPos T n i0 X = muAtPos T n i0.rev X := rfl
    have h_rev_succ : i0s.rev = i0.rev.castSucc := by
      rw [hi0s_eq]
      exact fin_rev_succ i0
    have h_mu_Sn : barMuAtPos T (n + 1) i0s X = muAtPos T (n + 1) i0.rev.castSucc X := by
      calc barMuAtPos T (n + 1) i0s X = muAtPos T (n + 1) i0s.rev X := rfl
        _ = muAtPos T (n + 1) i0.rev.castSucc X := by rw [h_rev_succ]
    have h_lt_rev : i0.rev.val < j.rev.val := by
      have hj_rev : j.rev.val = (n + 1) - (j.val + 1) := rfl
      have hi_rev : i0.rev.val = n - (i0.val + 1) := rfl
      omega
    have h_inter := etaAtPos_succ_muAtPos_castSucc_of_lt (T := T) n i0.rev j.rev h_lt_rev X
    calc (barDegeneracy (T := T) (R := R) (L := L) (n + 1) j.castSucc).app a ≫
            barFaceApp (T := T) (R := R) (L := L) (n + 1) i.succ a
        = R.functor.map (barEtaAtPos T (n + 1) j.castSucc X) ≫
            R.functor.map (barMuAtPos T (n + 1) i0s X) := by
          rw [h_face_Sn]; rfl
      _ = R.functor.map (etaAtPos T (n + 1) j.rev.succ X) ≫
            R.functor.map (muAtPos T (n + 1) i0.rev.castSucc X) := by
          rw [h_eta_Sn, h_mu_Sn]
      _ = R.functor.map (etaAtPos T (n + 1) j.rev.succ X ≫
            muAtPos T (n + 1) i0.rev.castSucc X) := by
          rw [← R.functor.map_comp]
      _ = R.functor.map (muAtPos T n i0.rev X ≫ etaAtPos T n j.rev X) := by
          rw [h_inter]
      _ = R.functor.map (muAtPos T n i0.rev X) ≫
            R.functor.map (etaAtPos T n j.rev X) := by
          rw [R.functor.map_comp]
      _ = R.functor.map (barMuAtPos T n i0 X) ≫
            R.functor.map (barEtaAtPos T n j X) := by
          rw [h_mu_n, h_eta_n]
      _ = barFaceApp (T := T) (R := R) (L := L) n i a ≫
            (barDegeneracy (T := T) (R := R) (L := L) n j).app a := by
          rw [h_face_n]; rfl

theorem barDegeneracy_of_gt {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : j.castSucc < i) :
    barDegeneracy (T := T) (R := R) (L := L) (n + 1) j.castSucc ≫
      barFace (T := T) (R := R) (L := L) (n + 1) i.succ =
    barFace (T := T) (R := R) (L := L) n i ≫
      barDegeneracy (T := T) (R := R) (L := L) n j := by
  ext a : 2
  exact barDegeneracyApp_of_gt (T := T) (R := R) (L := L) h a

end DegFaceOfGt

section BarData

variable {T : Monad C} {R : RightModule T D} {L : LeftModule A T}

noncomputable def barData (T : Monad C) (R : RightModule T D) (L : LeftModule A T) :
    SimplicialObject.Data (A ⥤ D) where
  obj := barObj T R L
  δ := fun {n} i => barFace (T := T) (R := R) (L := L) n i
  σ := fun {n} i => barDegeneracy (T := T) (R := R) (L := L) n i
  δ_comp_δ := fun {n} {i j} h => barFace_face (T := T) (R := R) (L := L) n i j h
  δ_comp_σ_of_le := fun {n} {i j} h =>
    barDegeneracy_of_le (T := T) (R := R) (L := L) (n := n) (i := i) (j := j) h
  δ_comp_σ_self := fun {n} {i} =>
    barDegeneracy_self (T := T) (R := R) (L := L) (n := n) (i := i)
  δ_comp_σ_succ := fun {n} {i} =>
    barDegeneracy_succ (T := T) (R := R) (L := L) (n := n) (i := i)
  δ_comp_σ_of_gt := fun {n} {i j} h =>
    barDegeneracy_of_gt (T := T) (R := R) (L := L) (n := n) (i := i) (j := j) h
  σ_comp_σ := fun {n} {i j} h =>
    barDegeneracy_sigma_sigma (T := T) (R := R) (L := L) (n := n) (i := i) (j := j) h

@[simp]
theorem barData_obj (T : Monad C) (R : RightModule T D) (L : LeftModule A T) :
    (barData T R L).obj = barObj T R L :=
  rfl

@[simp]
theorem barData_obj_n (T : Monad C) (R : RightModule T D) (L : LeftModule A T) (n : ℕ) :
    (barData T R L).obj n = barObj T R L n :=
  rfl

@[simp]
theorem barData_obj_obj (T : Monad C) (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) (a : A) :
    ((barData T R L).obj n).obj a = R.functor.obj ((monadPow T n).obj (L.functor.obj a)) :=
  rfl

@[simp]
theorem barData_obj_map (T : Monad C) (R : RightModule T D) (L : LeftModule A T)
    {n : ℕ} {a b : A} (f : a ⟶ b) :
    ((barData T R L).obj n).map f = R.functor.map ((monadPow T n).map (L.functor.map f)) :=
  rfl

@[simp]
theorem barData_δ (T : Monad C) (R : RightModule T D) (L : LeftModule A T)
    {n : ℕ} (i : Fin (n + 2)) :
    (barData T R L).δ i = barFace (T := T) (R := R) (L := L) n i :=
  rfl

@[simp]
theorem barData_δ_app (T : Monad C) (R : RightModule T D) (L : LeftModule A T)
    {n : ℕ} (i : Fin (n + 2)) (a : A) :
    ((barData T R L).δ i).app a = barFaceApp (T := T) (R := R) (L := L) n i a :=
  rfl

@[simp]
theorem barData_σ (T : Monad C) (R : RightModule T D) (L : LeftModule A T)
    {n : ℕ} (i : Fin (n + 1)) :
    (barData T R L).σ i = barDegeneracy (T := T) (R := R) (L := L) n i :=
  rfl

@[simp]
theorem barData_σ_app (T : Monad C) (R : RightModule T D) (L : LeftModule A T)
    {n : ℕ} (i : Fin (n + 1)) (a : A) :
    ((barData T R L).σ i).app a = R.functor.map (barEtaAtPos T n i (L.functor.obj a)) :=
  rfl

noncomputable def barGenRel (T : Monad C) (R : RightModule T D) (L : LeftModule A T) :
    SimplexCategoryGenRelᵒᵖ ⥤ (A ⥤ D) :=
  (barData T R L).toGenRelFunctor

@[simp]
theorem barGenRel_obj_op_mk (T : Monad C) (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) :
    (barGenRel T R L).obj (Opposite.op (SimplexCategoryGenRel.mk n)) = barObj T R L n :=
  rfl

theorem barGenRel_obj (T : Monad C) (R : RightModule T D) (L : LeftModule A T)
    (x : SimplexCategoryGenRelᵒᵖ) :
    (barGenRel T R L).obj x = barObj T R L (Opposite.unop x).len := by
  calc (barGenRel T R L).obj x
      = (barData T R L).obj (Opposite.unop x).len :=
        SimplicialObject.Data.toGenRelFunctor_obj (barData T R L) (x := x)
    _ = barObj T R L (Opposite.unop x).len := barData_obj_n T R L _

theorem barGenRel_map_δ_op (T : Monad C) (R : RightModule T D) (L : LeftModule A T)
    {n : ℕ} (i : Fin (n + 2)) :
    (barGenRel T R L).map (SimplexCategoryGenRel.δ (n := n) i).op =
      (barData T R L).δ i :=
  SimplicialObject.Data.toGenRelFunctor_map_δ_op (barData T R L) (n := n) i

theorem barGenRel_map_σ_op (T : Monad C) (R : RightModule T D) (L : LeftModule A T)
    {n : ℕ} (i : Fin (n + 1)) :
    (barGenRel T R L).map (SimplexCategoryGenRel.σ (n := n) i).op =
      (barData T R L).σ i :=
  SimplicialObject.Data.toGenRelFunctor_map_σ_op (barData T R L) (n := n) i

end BarData

section TwoSidedBar

variable {T : Monad C} {R : RightModule T D} {L : LeftModule A T}

/--
Cat-valued two-sided monadic bar as a thin instantiation of the generic `Data.toSimplicialObject`
transport.
-/
noncomputable def twoSidedBar (T : Monad C) (R : RightModule T D)
    (L : LeftModule A T) : SimplicialObject (A ⥤ D) :=
  (barData T R L).toSimplicialObject

@[simp]
theorem twoSidedBar_obj_op_mk (T : Monad C) (R : RightModule T D)
    (L : LeftModule A T) (n : ℕ) :
    (twoSidedBar T R L).obj (Opposite.op (SimplexCategory.mk n)) = barObj T R L n :=
  rfl

theorem twoSidedBar_obj (T : Monad C) (R : RightModule T D)
    (L : LeftModule A T) (Δ : SimplexCategoryᵒᵖ) :
    (twoSidedBar T R L).obj Δ = barObj T R L (Opposite.unop Δ).len := by
  have h := SimplicialObject.Data.toSimplicialObject_obj (barData T R L) (Δ := Δ)
  simp only [twoSidedBar] at h ⊢
  rw [h]
  rfl

@[simp]
theorem twoSidedBar_map_δ_op (T : Monad C) (R : RightModule T D)
    (L : LeftModule A T) {n : ℕ} (i : Fin (n + 2)) :
    (twoSidedBar T R L).map (SimplexCategory.δ i).op =
      barFace (T := T) (R := R) (L := L) n i := by
  have h := SimplicialObject.Data.toSimplicialObject_map_δ (barData T R L) (n := n) i
  simp only [twoSidedBar] at h ⊢
  rw [h]
  rfl

@[simp]
theorem twoSidedBar_map_σ_op (T : Monad C) (R : RightModule T D)
    (L : LeftModule A T) {n : ℕ} (i : Fin (n + 1)) :
    (twoSidedBar T R L).map (SimplexCategory.σ i).op =
      barDegeneracy (T := T) (R := R) (L := L) n i := by
  have h := SimplicialObject.Data.toSimplicialObject_map_σ (barData T R L) (n := n) i
  simp only [twoSidedBar] at h ⊢
  rw [h]
  rfl

@[simp]
theorem twoSidedBar_obj_obj (T : Monad C) (R : RightModule T D)
    (L : LeftModule A T) (n : ℕ) (a : A) :
    ((twoSidedBar T R L).obj (Opposite.op (SimplexCategory.mk n))).obj a =
      R.functor.obj ((monadPow T n).obj (L.functor.obj a)) :=
  rfl

@[simp]
theorem twoSidedBar_obj_map (T : Monad C) (R : RightModule T D)
    (L : LeftModule A T) {n : ℕ} {a b : A} (f : a ⟶ b) :
    ((twoSidedBar T R L).obj (Opposite.op (SimplexCategory.mk n))).map f =
      R.functor.map ((monadPow T n).map (L.functor.map f)) :=
  rfl

theorem twoSidedBar_obj_obj_Δ (T : Monad C) (R : RightModule T D)
    (L : LeftModule A T) (Δ : SimplexCategoryᵒᵖ) (a : A) :
    ((twoSidedBar T R L).obj Δ).obj a =
      R.functor.obj ((monadPow T (Opposite.unop Δ).len).obj (L.functor.obj a)) := by
  have h := twoSidedBar_obj T R L Δ
  cases h
  rfl

theorem twoSidedBar_obj_map_Δ (T : Monad C) (R : RightModule T D)
    (L : LeftModule A T) (Δ : SimplexCategoryᵒᵖ) {a b : A} (f : a ⟶ b) :
    ((twoSidedBar T R L).obj Δ).map f =
      R.functor.map ((monadPow T (Opposite.unop Δ).len).map (L.functor.map f)) := by
  have h := twoSidedBar_obj T R L Δ
  cases h
  rfl

@[simp]
theorem twoSidedBar_map_δ_op_app (T : Monad C) (R : RightModule T D)
    (L : LeftModule A T) {n : ℕ} (i : Fin (n + 2)) (a : A) :
    ((twoSidedBar T R L).map (SimplexCategory.δ i).op).app a =
      barFaceApp (T := T) (R := R) (L := L) n i a := by
  rw [twoSidedBar_map_δ_op]
  rfl

@[simp]
theorem twoSidedBar_map_σ_op_app (T : Monad C) (R : RightModule T D)
    (L : LeftModule A T) {n : ℕ} (i : Fin (n + 1)) (a : A) :
    ((twoSidedBar T R L).map (SimplexCategory.σ i).op).app a =
      R.functor.map (barEtaAtPos T n i (L.functor.obj a)) := by
  rw [twoSidedBar_map_σ_op]
  rfl

/--
Arbitrary simplex maps in the two-sided bar compute through `barGenRel`
after `fromSimplexCategory`.
-/
theorem twoSidedBar_map (T : Monad C) (R : RightModule T D)
    (L : LeftModule A T) {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    (twoSidedBar T R L).map f =
      (barGenRel T R L).map (SimplexCategoryGenRel.fromSimplexCategory.op.map f) :=
  rfl

end TwoSidedBar

end Monad
end CategoryTheory
