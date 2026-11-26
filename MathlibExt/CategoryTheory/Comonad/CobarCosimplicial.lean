/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Comonad.Cobar
public import MathlibExt.AlgebraicTopology.SimplicialObject.ToSimplicial

/-!
# The cosimplicial identities of two-sided comonadic cobar

Let `G` be a comonad on `C`, let `R : C ⥤ D` have right coaction `R → G ⋙ R`, and let `L : A ⥤
C` have left coaction `L → L ⋙ G`. The cobar degree functor is `R(G^n(L(-)))`. Its cofaces use
the two endpoint coactions and interior comultiplication, and its codegeneracies use counit
insertion, counting from the right-comodule end.

Coassociativity, the counit laws, and naturality give the coface, codegeneracy, and mixed
cosimplicial identities in every degree. The resulting cosimplicial object takes values in `A
⥤ D`. Coface zero is the right coaction, coface `n+1` is the left coaction, and interior
insertion positions are reversed by `Fin.rev`. All category and morphism universes remain
independent.

Reference: the categorical dual of J. P. May's two-sided bar construction in *The Geometry of
Iterated Loop Spaces*, Lecture Notes in Mathematics 271, Springer, 1972, Chapter 9,
Construction 9.6 and Remark 9.12, <https://doi.org/10.1007/BFb0067491>.
-/

@[expose] public section

namespace CategoryTheory
namespace Comonad

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type u₃} [Category.{v₃} A]

section CobarFaceHelpers

variable {G : Comonad C} {R : RightComodule G D} {L : LeftComodule A G}

/-- The cobar coface component at a zero-valued index.

If the coface index has value zero, its component is the iterated right-comodule coaction at
`L(a)`. -/
lemma cobarCofaceApp_of_val_zero {n : ℕ} {a : A} {i : Fin (n + 2)}
    (hi : i.val = 0) :
    cobarCofaceApp (G := G) (R := R) (L := L) n i a =
      rightCoactionPow G R n (L.functor.obj a) := by
  unfold cobarCofaceApp
  rw [dite_eq_left hi]

/-- The cobar coface component at the final index.

If the coface index has value `n+1`, its component is the left coaction mapped through `G^n`
and `R`. -/
lemma cobarCofaceApp_of_val_last {n : ℕ} {a : A} {i : Fin (n + 2)}
    (hi : i.val = n + 1) :
    cobarCofaceApp (G := G) (R := R) (L := L) n i a =
      R.functor.map ((comonadPow G n).map (L.coaction.app a)) := by
  have h0 : ¬ (i.val = 0) := by omega
  unfold cobarCofaceApp
  rw [dite_eq_right h0, dite_eq_left hi]

/-- The cobar coface component at an interior index.

For an index of value `k+1` with `k : Fin n`, its component is `R` applied to comultiplication
insertion at reversed position `k.rev`. -/
lemma cobarCofaceApp_of_middle {n : ℕ} {a : A} {i : Fin (n + 2)} {k : Fin n}
    (hk : i.val = k.val + 1) :
    cobarCofaceApp (G := G) (R := R) (L := L) n i a =
      R.functor.map (cobarDeltaAtPos G n k (L.functor.obj a)) := by
  have h_eq : i = ⟨k.val + 1, by omega⟩ := by
    apply Fin.ext
    simp [hk]
  rw [h_eq]
  exact cobarCofaceApp_middle (G := G) (R := R) (L := L) n k a

end CobarFaceHelpers

section DeltaCalculus

variable (G : Comonad C)

/-- The innermost comultiplication insertion formula.

Insertion at position zero in `G^(n+1)(X)` is `G^n.map(δ_X)`. -/
lemma deltaAtPos_zero_eq (n : ℕ) (X : C) :
    deltaAtPos G (n + 1) ⟨0, by omega⟩ X =
      (comonadPow G n).map (G.δ.app X) := rfl

/-- The successor-position comultiplication insertion formula.

Insertion at position `k+1` is insertion at position `k` one power lower, evaluated at `G(X)`. -/
lemma deltaAtPos_succ_eq (n : ℕ) (k : Fin n) (X : C) :
    deltaAtPos G (n + 1) ⟨k.val + 1, by omega⟩ X =
      deltaAtPos G n k (G.toFunctor.obj X) := by
  have : (⟨k.val, by omega⟩ : Fin n) = k := by
    ext
    rfl
  calc deltaAtPos G (n + 1) ⟨k.val + 1, by omega⟩ X
      = deltaAtPos G n ⟨k.val, by omega⟩ (G.toFunctor.obj X) := rfl
    _ = deltaAtPos G n k (G.toFunctor.obj X) := by rw [this]

/-- The coassociativity identity of adjacent comultiplication insertions.

After inserting at `k`, inserting at the two positions of the resulting split factor gives the
same composite. -/
theorem deltaAtPos_adjacent (n : ℕ) (k : Fin n) (X : C) :
    deltaAtPos G n k X ≫ deltaAtPos G (n + 1) ⟨k.val + 1, by omega⟩ X =
      deltaAtPos G n k X ≫ deltaAtPos G (n + 1) ⟨k.val, by omega⟩ X := by
  induction n generalizing X with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    match k with
    | ⟨0, _⟩ =>
      have h1 : deltaAtPos G (n + 1 + 1) ⟨0 + 1, by omega⟩ X =
          (comonadPow G n).map (G.δ.app (G.toFunctor.obj X)) := rfl
      have h2 : deltaAtPos G (n + 1) ⟨0, by omega⟩ X =
          (comonadPow G n).map (G.δ.app X) := rfl
      have h3 : deltaAtPos G (n + 1 + 1) ⟨0, by omega⟩ X =
          (comonadPow G (n + 1)).map (G.δ.app X) := rfl
      rw [h1, h2, h3]
      calc
        (comonadPow G n).map (G.δ.app X) ≫
                (comonadPow G n).map (G.δ.app (G.toFunctor.obj X))
              = (comonadPow G n).map
                (G.δ.app X ≫ G.δ.app (G.toFunctor.obj X)) := by
                rw [← (comonadPow G n).map_comp]
          _ = (comonadPow G n).map
                (G.δ.app X ≫ G.toFunctor.map (G.δ.app X)) := by
                rw [G.coassoc X]
          _ = (comonadPow G n).map (G.δ.app X) ≫
                (comonadPow G n).map (G.toFunctor.map (G.δ.app X)) := by
                rw [(comonadPow G n).map_comp]
    | ⟨k + 1, hk⟩ =>
      let k0 : Fin n := ⟨k, by omega⟩
      have hA : deltaAtPos G (n + 1 + 1) ⟨k + 1 + 1, by omega⟩ X =
          deltaAtPos G (n + 1) ⟨k + 1, by omega⟩ (G.toFunctor.obj X) := rfl
      have hB : deltaAtPos G (n + 1) ⟨k + 1, by omega⟩ X =
          deltaAtPos G n k0 (G.toFunctor.obj X) := rfl
      have hC : deltaAtPos G (n + 1 + 1) ⟨k + 1, by omega⟩ X =
          deltaAtPos G (n + 1) ⟨k0.val, by omega⟩ (G.toFunctor.obj X) := rfl
      calc deltaAtPos G (n + 1) ⟨k + 1, by omega⟩ X ≫
              deltaAtPos G (n + 1 + 1) ⟨k + 1 + 1, by omega⟩ X
            = deltaAtPos G n k0 (G.toFunctor.obj X) ≫
              deltaAtPos G (n + 1) ⟨k + 1, by omega⟩
                (G.toFunctor.obj X) := by
              rw [hB, hA]
        _ = deltaAtPos G n k0 (G.toFunctor.obj X) ≫
              deltaAtPos G (n + 1) ⟨k0.val + 1, by omega⟩
                (G.toFunctor.obj X) := rfl
        _ = deltaAtPos G n k0 (G.toFunctor.obj X) ≫
              deltaAtPos G (n + 1) ⟨k0.val, by omega⟩
                (G.toFunctor.obj X) :=
          ih k0 (G.toFunctor.obj X)
        _ = deltaAtPos G (n + 1) ⟨k + 1, by omega⟩ X ≫
              deltaAtPos G (n + 1 + 1) ⟨k + 1, by omega⟩ X := by
          rw [← hB, ← hC]

/-- The interchange identity of separated comultiplication insertions.

If `i+1<j`, insertion at `i` followed by insertion at `j` equals insertion at `j-1` followed
by insertion at `i`, with the indicated power degrees. -/
theorem deltaAtPos_separated (n : ℕ) (i : Fin n) (j : Fin (n + 1))
    (h : i.val + 1 < j.val) (X : C) :
    deltaAtPos G n i X ≫ deltaAtPos G (n + 1) j X =
      deltaAtPos G n ⟨j.val - 1, by omega⟩ X ≫
        deltaAtPos G (n + 1) ⟨i.val, by omega⟩ X := by
  induction n generalizing X with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    have hj_pos : 0 < j.val := by omega
    let j0 : Fin (n + 1) := ⟨j.val - 1, by omega⟩
    have hj_eq : j = ⟨j0.val + 1, by omega⟩ := by
      apply Fin.ext
      simp [j0]
      omega
    have hmu_j : deltaAtPos G (n + 2) j X =
        deltaAtPos G (n + 1) j0 (G.toFunctor.obj X) := by
      rw [hj_eq]
      exact deltaAtPos_succ_eq G (n + 1) j0 X
    by_cases hi0 : i.val = 0
    · have hi_eq : i = ⟨0, by omega⟩ := by
        apply Fin.ext
        omega
      have hj0_ge1 : 1 ≤ j0.val := by
        simp [j0]
        omega
      let k0 : Fin n := ⟨j0.val - 1, by omega⟩
      have hj0_eq : j0 = ⟨k0.val + 1, by omega⟩ := by
        apply Fin.ext
        simp [k0, j0]
        omega
      have hmu_j0 : deltaAtPos G (n + 1) j0 X =
          deltaAtPos G n k0 (G.toFunctor.obj X) := by
        rw [hj0_eq]
        exact deltaAtPos_succ_eq G n k0 X
      have hmu_j0_T : deltaAtPos G (n + 1) j0 (G.toFunctor.obj X) =
          deltaAtPos G n k0 (G.toFunctor.obj (G.toFunctor.obj X)) := by
        rw [hj0_eq]
        exact deltaAtPos_succ_eq G n k0 (G.toFunctor.obj X)
      have hmu_i : deltaAtPos G (n + 1) i X =
          (comonadPow G n).map (G.δ.app X) := by
        rw [hi_eq]
        rfl
      have hmu_R1 : deltaAtPos G (n + 2) ⟨i.val, by omega⟩ X =
          (comonadPow G (n + 1)).map (G.δ.app X) := by
        have hi0' : i.val = 0 := by omega
        have : (⟨i.val, by omega⟩ : Fin (n + 2)) = ⟨0, by omega⟩ := by
          apply Fin.ext
          omega
        rw [this]
        rfl
      have hR2 : deltaAtPos G (n + 1) ⟨j.val - 1, by omega⟩ X =
          deltaAtPos G (n + 1) j0 X := by
        have : (⟨j.val - 1, by omega⟩ : Fin (n + 1)) = j0 := by
          apply Fin.ext
          simp [j0]
        rw [this]
      rw [hmu_j, hmu_i, hmu_R1, hR2, hmu_j0_T, hmu_j0]
      exact deltaAtPos_naturality G n k0 (G.δ.app X)
    · have hi_ge1 : 1 ≤ i.val := by omega
      let i0 : Fin n := ⟨i.val - 1, by omega⟩
      have hi_eq : i = ⟨i0.val + 1, by omega⟩ := by
        apply Fin.ext
        simp [i0]
        omega
      have hj0_cond : i0.val + 1 < j0.val := by
        simp [i0, j0]
        omega
      have hmu_i : deltaAtPos G (n + 1) i X =
          deltaAtPos G n i0 (G.toFunctor.obj X) := by
        rw [hi_eq]
        exact deltaAtPos_succ_eq G n i0 X
      have hR1 : deltaAtPos G (n + 2) ⟨i.val, by omega⟩ X =
          deltaAtPos G (n + 1) ⟨i0.val, by omega⟩ (G.toFunctor.obj X) := by
        have : (⟨i.val, by omega⟩ : Fin (n + 2)) = ⟨i0.val + 1, by omega⟩ := by
          apply Fin.ext
          simp [i0]
          omega
        rw [this]
        exact deltaAtPos_succ_eq G (n + 1) ⟨i0.val, by omega⟩ X
      have hR2 : deltaAtPos G (n + 1) ⟨j.val - 1, by omega⟩ X =
          deltaAtPos G (n + 1) j0 X := by
        have : (⟨j.val - 1, by omega⟩ : Fin (n + 1)) = j0 := by
          apply Fin.ext
          simp [j0]
        rw [this]
      have hj0_ge1 : 1 ≤ j0.val := by
        have := hj0_cond
        omega
      let k0 : Fin n := ⟨j0.val - 1, by omega⟩
      have hj0_eq : j0 = ⟨k0.val + 1, by omega⟩ := by
        apply Fin.ext
        simp [k0, j0]
        omega
      have hmu_j0 : deltaAtPos G (n + 1) j0 X =
          deltaAtPos G n k0 (G.toFunctor.obj X) := by
        rw [hj0_eq]
        exact deltaAtPos_succ_eq G n k0 X
      rw [hmu_j, hmu_i, hR1, hR2, hmu_j0]
      have ih_eq := ih i0 j0 hj0_cond (G.toFunctor.obj X)
      have h_eq2 : deltaAtPos G n ⟨j0.val - 1, by omega⟩ (G.toFunctor.obj X) =
          deltaAtPos G n k0 (G.toFunctor.obj X) := by
        have : (⟨j0.val - 1, by omega⟩ : Fin n) = k0 := by
          apply Fin.ext
          simp [k0]
        rw [this]
      rw [h_eq2] at ih_eq
      exact ih_eq

/-- The ordered comultiplication insertion identity.

For `i ≤ j`, `δ_n[i] ≫ δ_(n+1)[j+1] = δ_n[j] ≫ δ_(n+1)[i]` in left-end insertion coordinates. -/
theorem deltaAtPos_face_face (n : ℕ) (i j : Fin n) (h : i ≤ j) (X : C) :
    deltaAtPos G n i X ≫ deltaAtPos G (n + 1) j.succ X =
      deltaAtPos G n j X ≫ deltaAtPos G (n + 1) i.castSucc X := by
  by_cases hij : i = j
  · subst hij
    have h_succ : i.succ = (⟨i.val + 1, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp
    have h_cast : (⟨i.val, by omega⟩ : Fin (n + 1)) = i.castSucc := by
      apply Fin.ext
      simp
    have h_adj := deltaAtPos_adjacent (G := G) n i X
    calc deltaAtPos G n i X ≫ deltaAtPos G (n + 1) i.succ X
          = deltaAtPos G n i X ≫
            deltaAtPos G (n + 1) (⟨i.val + 1, by omega⟩ : Fin (n + 1)) X := by
            rw [h_succ]
      _ = deltaAtPos G n i X ≫
            deltaAtPos G (n + 1) (⟨i.val, by omega⟩ : Fin (n + 1)) X := h_adj
      _ = deltaAtPos G n i X ≫ deltaAtPos G (n + 1) i.castSucc X := by
        rw [h_cast]
  · have h_le : i.val ≤ j.val := h
    have h_ne : i.val ≠ j.val := by
      intro heq
      apply hij
      apply Fin.ext
      exact heq
    have h_lt_val : i.val < j.val := Nat.lt_of_le_of_ne h_le h_ne
    have h_lt : i.val + 1 < j.succ.val := by
      simp
      omega
    have h_sep := deltaAtPos_separated (G := G) n i j.succ h_lt X
    have h_cast : (⟨i.val, by omega⟩ : Fin (n + 1)) = i.castSucc := by
      apply Fin.ext
      simp
    have h_j : (⟨j.succ.val - 1, by omega⟩ : Fin n) = j := by
      apply Fin.ext
      simp
    calc deltaAtPos G n i X ≫ deltaAtPos G (n + 1) j.succ X
          = deltaAtPos G n (⟨j.succ.val - 1, by omega⟩ : Fin n) X ≫
            deltaAtPos G (n + 1) (⟨i.val, by omega⟩ : Fin (n + 1)) X :=
        h_sep
      _ = deltaAtPos G n (⟨j.succ.val - 1, by omega⟩ : Fin n) X ≫
            deltaAtPos G (n + 1) i.castSucc X := by
        rw [h_cast]
      _ = deltaAtPos G n j X ≫ deltaAtPos G (n + 1) i.castSucc X := by
        rw [h_j]

end DeltaCalculus

section EpsilonCalculus

variable (G : Comonad C)

/-- The innermost counit insertion formula.

Counit insertion at position zero from `G^(n+2)(X)` is `G^(n+1).map(ε_X)`. -/
lemma epsilonAtPos_zero_eq (n : ℕ) (X : C) :
    epsilonAtPos G (n + 1) ⟨0, by omega⟩ X =
      (comonadPow G (n + 1)).map (G.ε.app X) := rfl

/-- The successor-position counit insertion formula.

Counit insertion at position `k+1` is the preceding-degree insertion at `k`, evaluated at
`G(X)`. -/
lemma epsilonAtPos_succ_eq (n : ℕ) (k : Fin (n + 1)) (X : C) :
    epsilonAtPos G (n + 1) ⟨k.val + 1, by omega⟩ X =
      epsilonAtPos G n k (G.toFunctor.obj X) := rfl

/-- The ordered counit insertion identity.

For `i ≤ j`, contracting at `i` and then `j` equals contracting at `j+1` and then `i`, with
the stated power degrees. -/
theorem epsilonAtPos_deg_deg (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) (X : C) :
    epsilonAtPos G (n + 1) i.castSucc X ≫ epsilonAtPos G n j X =
      epsilonAtPos G (n + 1) j.succ X ≫ epsilonAtPos G n i X := by
  induction n generalizing X with
  | zero =>
    have hi0 : i.val = 0 := by
      have := i.isLt
      omega
    have hj0 : j.val = 0 := by
      have := j.isLt
      omega
    have hi_eq : i = ⟨0, by omega⟩ := by
      ext
      exact hi0
    have hj_eq : j = ⟨0, by omega⟩ := by
      ext
      exact hj0
    rw [hi_eq, hj_eq]
    have hcs : (Fin.castSucc (⟨0, by omega⟩ : Fin 1) : Fin 2) = ⟨0, by omega⟩ := by
      ext
      simp
    have hs : (Fin.succ (⟨0, by omega⟩ : Fin 1) : Fin 2) = ⟨1, by omega⟩ := by
      ext
      simp
    rw [hcs, hs]
    change (comonadPow G 1).map (G.ε.app X) ≫ G.ε.app X =
      epsilonAtPos G 1 ⟨1, by omega⟩ X ≫ G.ε.app X
    have h1 : epsilonAtPos G 1 ⟨1, by omega⟩ X =
        G.ε.app (G.toFunctor.obj X) := rfl
    rw [h1]
    simp
  | succ n ih =>
    by_cases hi0 : i.val = 0
    · have hi_eq : i = ⟨0, by omega⟩ := by
        ext
        omega
      rw [hi_eq]
      by_cases hj0 : j.val = 0
      · have hj_eq : j = ⟨0, by omega⟩ := by
          ext
          omega
        rw [hj_eq]
        have hcs0 : (Fin.castSucc (⟨0, by omega⟩ : Fin (n + 2)) :
            Fin (n + 3)) = ⟨0, by omega⟩ := by
          ext
          simp
        have hs0 : (Fin.succ (⟨0, by omega⟩ : Fin (n + 2)) :
            Fin (n + 3)) = ⟨1, by omega⟩ := by
          ext
          simp
        rw [hcs0, hs0]
        have inner' : G.toFunctor.map (G.ε.app X) ≫ G.ε.app X =
            G.ε.app (G.toFunctor.obj X) ≫ G.ε.app X :=
          G.ε.naturality (G.ε.app X)
        calc (comonadPow G (n + 2)).map (G.ε.app X) ≫
                (comonadPow G (n + 1)).map (G.ε.app X)
              = (comonadPow G (n + 1)).map (G.toFunctor.map (G.ε.app X)) ≫
                (comonadPow G (n + 1)).map (G.ε.app X) := rfl
          _ = (comonadPow G (n + 1)).map
                (G.toFunctor.map (G.ε.app X) ≫ G.ε.app X) := by
            rw [← (comonadPow G (n + 1)).map_comp]
          _ = (comonadPow G (n + 1)).map
                (G.ε.app (G.toFunctor.obj X) ≫ G.ε.app X) := by
            rw [inner']
          _ = (comonadPow G (n + 1)).map (G.ε.app (G.toFunctor.obj X)) ≫
                (comonadPow G (n + 1)).map (G.ε.app X) := by
            rw [(comonadPow G (n + 1)).map_comp]
          _ = epsilonAtPos G (n + 2) ⟨1, by omega⟩ X ≫
                epsilonAtPos G (n + 1) ⟨0, by omega⟩ X := rfl
      · have hj_pos : 0 < j.val := by omega
        let j0 : Fin (n + 1) := ⟨j.val - 1, by omega⟩
        have hj_eq : j = ⟨j0.val + 1, by omega⟩ := by
          apply Fin.ext
          simp [j0]
          omega
        rw [hj_eq]
        have hcs0 : (Fin.castSucc (⟨0, by omega⟩ : Fin (n + 2)) :
            Fin (n + 3)) = ⟨0, by omega⟩ := by
          ext
          simp
        rw [hcs0]
        have h_eps_j : epsilonAtPos G (n + 1) ⟨j0.val + 1, by omega⟩ X =
            epsilonAtPos G n j0 (G.toFunctor.obj X) := rfl
        have h_succ_j : (Fin.succ ⟨j0.val + 1, by omega⟩ :
            Fin (n + 3)) = ⟨j0.val + 2, by omega⟩ := by
          ext
          simp
        change (comonadPow G (n + 2)).map (G.ε.app X) ≫
              epsilonAtPos G (n + 1) ⟨j0.val + 1, by omega⟩ X =
            epsilonAtPos G (n + 2) (Fin.succ ⟨j0.val + 1, by omega⟩) X ≫
              (comonadPow G (n + 1)).map (G.ε.app X)
        rw [h_succ_j]
        have h_eps_succ : epsilonAtPos G (n + 2) ⟨j0.val + 2, by omega⟩ X =
            epsilonAtPos G (n + 1) ⟨j0.val + 1, by omega⟩
              (G.toFunctor.obj X) := rfl
        rw [h_eps_j, h_eps_succ]
        calc (comonadPow G (n + 2)).map (G.ε.app X) ≫
                epsilonAtPos G n j0 (G.toFunctor.obj X)
              = (comonadPow G (n + 1)).map (G.toFunctor.map (G.ε.app X)) ≫
                epsilonAtPos G n j0 (G.toFunctor.obj X) := rfl
          _ = epsilonAtPos G n j0 (G.toFunctor.obj (G.toFunctor.obj X)) ≫
                (comonadPow G n).map (G.toFunctor.map (G.ε.app X)) := by
            have h_nat := epsilonAtPos_naturality G n j0
              (f := G.toFunctor.map (G.ε.app X))
            simpa using h_nat
          _ = epsilonAtPos G (n + 1) ⟨j0.val + 1, by omega⟩ (G.toFunctor.obj X) ≫
                (comonadPow G (n + 1)).map (G.ε.app X) := rfl
    · have hi_pos : 0 < i.val := by omega
      have hj_pos : 0 < j.val := by
        have : i.val ≤ j.val := by
          simpa only [Fin.le_def] using h
        omega
      let i0 : Fin (n + 1) := ⟨i.val - 1, by omega⟩
      let j0 : Fin (n + 1) := ⟨j.val - 1, by omega⟩
      have hi_eq : i = ⟨i0.val + 1, by omega⟩ := by
        apply Fin.ext
        simp [i0]
        omega
      have hj_eq : j = ⟨j0.val + 1, by omega⟩ := by
        apply Fin.ext
        simp [j0]
        omega
      rw [hi_eq, hj_eq]
      have hi0_le_j0 : i0 ≤ j0 := by
        simp [Fin.le_def, i0, j0]
        omega
      have h_i_cast : (Fin.castSucc ⟨i0.val + 1, by omega⟩ :
          Fin (n + 3)) = ⟨i0.val + 1, by omega⟩ := by
        ext
        simp
      have h_j_succ : (Fin.succ ⟨j0.val + 1, by omega⟩ :
          Fin (n + 3)) = ⟨j0.val + 2, by omega⟩ := by
        ext
        simp
      rw [h_i_cast, h_j_succ]
      have h_eps_j : epsilonAtPos G (n + 1) ⟨j0.val + 1, by omega⟩ X =
          epsilonAtPos G n j0 (G.toFunctor.obj X) := rfl
      have h_eps_i : epsilonAtPos G (n + 1) ⟨i0.val + 1, by omega⟩ X =
          epsilonAtPos G n i0 (G.toFunctor.obj X) := rfl
      have h_eps_i_cast : epsilonAtPos G (n + 2) ⟨i0.val + 1, by omega⟩ X =
          epsilonAtPos G (n + 1) i0.castSucc (G.toFunctor.obj X) := by
        have h1 : (⟨i0.val + 1, by omega⟩ : Fin (n + 3)) =
            (Fin.castSucc i0).succ := by
          ext
          simp [Fin.castSucc, Fin.succ]
        rw [h1]
        rfl
      have h_eps_j_succ : epsilonAtPos G (n + 2) ⟨j0.val + 2, by omega⟩ X =
          epsilonAtPos G (n + 1) ⟨j0.val + 1, by omega⟩
            (G.toFunctor.obj X) := rfl
      have h_j_eq : (⟨j0.val + 1, by omega⟩ : Fin (n + 2)) = j0.succ := by
        ext
        simp [Fin.succ]
      calc epsilonAtPos G (n + 2) ⟨i0.val + 1, by omega⟩ X ≫
              epsilonAtPos G (n + 1) ⟨j0.val + 1, by omega⟩ X
          = epsilonAtPos G (n + 1) i0.castSucc (G.toFunctor.obj X) ≫
              epsilonAtPos G n j0 (G.toFunctor.obj X) := by
            rw [h_eps_i_cast, h_eps_j]
        _ = epsilonAtPos G (n + 1) j0.succ (G.toFunctor.obj X) ≫
              epsilonAtPos G n i0 (G.toFunctor.obj X) := by
            exact ih i0 j0 hi0_le_j0 (G.toFunctor.obj X)
        _ = epsilonAtPos G (n + 1) ⟨j0.val + 1, by omega⟩
              (G.toFunctor.obj X) ≫
              epsilonAtPos G n i0 (G.toFunctor.obj X) := by
            rw [h_j_eq]
        _ = epsilonAtPos G (n + 2) ⟨j0.val + 2, by omega⟩ X ≫
              epsilonAtPos G (n + 1) ⟨i0.val + 1, by omega⟩ X := by
            rw [h_eps_j_succ, h_eps_i]

end EpsilonCalculus

section DeltaEpsilon

variable (G : Comonad C)

/-- The first counit identity after a comultiplication insertion.

Comultiplication at position `i` followed by counit contraction at `i.castSucc` is the
identity. -/
theorem deltaAtPos_epsilonAtPos_castSucc (n : ℕ) (i : Fin n) (X : C) :
    deltaAtPos G n i X ≫ epsilonAtPos G n i.castSucc X = 𝟙 _ := by
  induction n generalizing X with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    have hiv : i.val < n + 1 := i.isLt
    by_cases h0 : i.val = 0
    · have hi_eq : i = ⟨0, by omega⟩ := by ext; omega
      rw [hi_eq]
      have hcast0 : (Fin.castSucc (⟨0, by omega⟩ : Fin (n + 1)) :
          Fin (n + 2)) = ⟨0, by omega⟩ := by
        ext; simp
      have hδ0 : deltaAtPos G (n + 1) (⟨0, by omega⟩ : Fin (n + 1)) X =
          (comonadPow G n).map (G.δ.app X) := rfl
      have hε0 : epsilonAtPos G (n + 1) (⟨0, by omega⟩ : Fin (n + 2)) X =
          (comonadPow G (n + 1)).map (G.ε.app X) := rfl
      calc
        deltaAtPos G (n + 1) (⟨0, by omega⟩ : Fin (n + 1)) X ≫
            epsilonAtPos G (n + 1)
              (Fin.castSucc (⟨0, by omega⟩ : Fin (n + 1))) X
            = deltaAtPos G (n + 1) (⟨0, by omega⟩ : Fin (n + 1)) X ≫
              (comonadPow G (n + 1)).map (G.ε.app X) := by
          rw [hcast0, hε0]
        _ = (comonadPow G n).map (G.δ.app X) ≫
            (comonadPow G (n + 1)).map (G.ε.app X) := by
          rw [hδ0]
        _ = (comonadPow G n).map (G.δ.app X) ≫
            (comonadPow G n).map (G.toFunctor.map (G.ε.app X)) := rfl
        _ = (comonadPow G n).map
            (G.δ.app X ≫ G.toFunctor.map (G.ε.app X)) := by
          rw [← (comonadPow G n).map_comp]
        _ = (comonadPow G n).map (𝟙 _) := by
          rw [G.right_counit X]
        _ = 𝟙 _ := by
          rw [(comonadPow G n).map_id]
    · have hpos : 0 < i.val := by omega
      set i0 : Fin n := ⟨i.val - 1, by omega⟩ with hi0_def
      have hi_eq : i = ⟨i0.val + 1, by omega⟩ := by
        ext; simp [hi0_def]; omega
      rw [hi_eq]
      have hcast_eq : (Fin.castSucc (⟨i0.val + 1, by omega⟩ : Fin (n + 1)) :
          Fin (n + 2)) = ⟨i0.val + 1, by omega⟩ := by
        ext; simp
      have hδ_succ : deltaAtPos G (n + 1) (⟨i0.val + 1, by omega⟩ :
          Fin (n + 1)) X =
          deltaAtPos G n i0 (G.toFunctor.obj X) :=
        deltaAtPos_succ_eq G n i0 X
      have hε_cast : epsilonAtPos G (n + 1) (⟨i0.val + 1, by omega⟩ :
          Fin (n + 2)) X =
          epsilonAtPos G n i0.castSucc (G.toFunctor.obj X) := by
        have hcs : (i0.castSucc : Fin (n + 1)) = ⟨i0.val, by omega⟩ := by
          ext; simp [hi0_def]
        calc
          epsilonAtPos G (n + 1) ⟨i0.val + 1, by omega⟩ X =
              epsilonAtPos G n ⟨i0.val, by omega⟩
                (G.toFunctor.obj X) := rfl
          _ = epsilonAtPos G n i0.castSucc (G.toFunctor.obj X) := by
            have : (⟨i0.val, by omega⟩ : Fin (n + 1)) = i0.castSucc := by
              ext; simp [hi0_def]
            rw [this]
      calc
        deltaAtPos G (n + 1) (⟨i0.val + 1, by omega⟩ : Fin (n + 1)) X ≫
            epsilonAtPos G (n + 1)
              (Fin.castSucc (⟨i0.val + 1, by omega⟩ : Fin (n + 1))) X
            = deltaAtPos G (n + 1) (⟨i0.val + 1, by omega⟩ :
                Fin (n + 1)) X ≫
              epsilonAtPos G (n + 1) (⟨i0.val + 1, by omega⟩ :
                Fin (n + 2)) X := by
          rw [hcast_eq]
        _ = deltaAtPos G n i0 (G.toFunctor.obj X) ≫
            epsilonAtPos G n i0.castSucc (G.toFunctor.obj X) := by
          rw [hε_cast, hδ_succ]
        _ = 𝟙 _ := ih i0 (G.toFunctor.obj X)

/-- The second counit identity after a comultiplication insertion.

Comultiplication at position `i` followed by counit contraction at `i.succ` is the identity. -/
theorem deltaAtPos_epsilonAtPos_succ (n : ℕ) (i : Fin n) (X : C) :
    deltaAtPos G n i X ≫ epsilonAtPos G n i.succ X = 𝟙 _ := by
  induction n generalizing X with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    have hiv : i.val < n + 1 := i.isLt
    by_cases h0 : i.val = 0
    · have hi_eq : i = ⟨0, by omega⟩ := by ext; omega
      rw [hi_eq]
      have hsucc0 : (Fin.succ (⟨0, by omega⟩ : Fin (n + 1)) :
          Fin (n + 2)) = ⟨1, by omega⟩ := by
        ext; simp
      have hδ0 : deltaAtPos G (n + 1) (⟨0, by omega⟩ : Fin (n + 1)) X =
          (comonadPow G n).map (G.δ.app X) := rfl
      have hε_succ0 : epsilonAtPos G (n + 1) (⟨1, by omega⟩ : Fin (n + 2)) X =
          epsilonAtPos G n (⟨0, by omega⟩ : Fin (n + 1))
            (G.toFunctor.obj X) := rfl
      have hε_map : epsilonAtPos G n (⟨0, by omega⟩ : Fin (n + 1))
          (G.toFunctor.obj X) =
          (comonadPow G n).map (G.ε.app (G.toFunctor.obj X)) := by
        cases n with
        | zero => rfl
        | succ _ => rfl
      calc
        deltaAtPos G (n + 1) (⟨0, by omega⟩ : Fin (n + 1)) X ≫
            epsilonAtPos G (n + 1)
              (Fin.succ (⟨0, by omega⟩ : Fin (n + 1))) X
            = deltaAtPos G (n + 1) (⟨0, by omega⟩ : Fin (n + 1)) X ≫
              epsilonAtPos G (n + 1) (⟨1, by omega⟩ : Fin (n + 2)) X := by
          rw [hsucc0]
        _ = (comonadPow G n).map (G.δ.app X) ≫
            epsilonAtPos G n (⟨0, by omega⟩ : Fin (n + 1))
              (G.toFunctor.obj X) := by
          rw [hδ0, hε_succ0]
        _ = (comonadPow G n).map (G.δ.app X) ≫
            (comonadPow G n).map (G.ε.app (G.toFunctor.obj X)) := by
          rw [hε_map]
        _ = (comonadPow G n).map
            (G.δ.app X ≫ G.ε.app (G.toFunctor.obj X)) := by
          rw [← (comonadPow G n).map_comp]
        _ = (comonadPow G n).map (𝟙 _) := by
          rw [G.left_counit X]
        _ = 𝟙 _ := by
          rw [(comonadPow G n).map_id]
    · have hpos : 0 < i.val := by omega
      set i0 : Fin n := ⟨i.val - 1, by omega⟩ with hi0_def
      have hi_eq : i = ⟨i0.val + 1, by omega⟩ := by
        ext; simp [hi0_def]; omega
      rw [hi_eq]
      have hsucc_eq : (Fin.succ (⟨i0.val + 1, by omega⟩ : Fin (n + 1)) :
          Fin (n + 2)) = ⟨i0.val + 2, by omega⟩ := by
        ext; simp
      have hδ_succ : deltaAtPos G (n + 1) (⟨i0.val + 1, by omega⟩ :
          Fin (n + 1)) X =
          deltaAtPos G n i0 (G.toFunctor.obj X) :=
        deltaAtPos_succ_eq G n i0 X
      have hε_succ2 : epsilonAtPos G (n + 1) (⟨i0.val + 2, by omega⟩ :
          Fin (n + 2)) X =
          epsilonAtPos G n i0.succ (G.toFunctor.obj X) := by
        have h1 : epsilonAtPos G (n + 1) ⟨i0.val + 1 + 1, by omega⟩ X =
            epsilonAtPos G n ⟨i0.val + 1, by omega⟩
              (G.toFunctor.obj X) := rfl
        have h2 : (i0.succ : Fin (n + 1)) = ⟨i0.val + 1, by omega⟩ := by
          ext; simp [Fin.succ, hi0_def]
        have heq : (⟨i0.val + 2, by omega⟩ : Fin (n + 2)) =
            ⟨i0.val + 1 + 1, by omega⟩ := by
          ext; rfl
        calc
          epsilonAtPos G (n + 1) ⟨i0.val + 2, by omega⟩ X
              = epsilonAtPos G (n + 1) ⟨i0.val + 1 + 1, by omega⟩ X := by
            rw [heq]
          _ = epsilonAtPos G n ⟨i0.val + 1, by omega⟩
              (G.toFunctor.obj X) := h1
          _ = epsilonAtPos G n i0.succ (G.toFunctor.obj X) := by rw [← h2]
      calc
        deltaAtPos G (n + 1) (⟨i0.val + 1, by omega⟩ : Fin (n + 1)) X ≫
            epsilonAtPos G (n + 1)
              (Fin.succ (⟨i0.val + 1, by omega⟩ : Fin (n + 1))) X
            = deltaAtPos G n i0 (G.toFunctor.obj X) ≫
              epsilonAtPos G (n + 1) (⟨i0.val + 2, by omega⟩ :
                Fin (n + 2)) X := by
          rw [hsucc_eq, hδ_succ]
        _ = deltaAtPos G n i0 (G.toFunctor.obj X) ≫
            epsilonAtPos G n i0.succ (G.toFunctor.obj X) := by
          rw [hε_succ2]
        _ = 𝟙 _ := ih i0 (G.toFunctor.obj X)

end DeltaEpsilon

section CoactionCalculus

variable {G : Comonad C} {R : RightComodule G D} {L : LeftComodule A G}

/-- The right-coaction coassociativity identity at the outer insertion.

The iterated right coaction followed by comultiplication at the outermost left-end position
equals two successive iterated right coactions. -/
theorem rightCoactionPow_coassoc_last (n : ℕ) (X : C) :
    rightCoactionPow G R n X ≫
      R.functor.map (deltaAtPos G (n + 1) ⟨n, by omega⟩ X) =
    rightCoactionPow G R n X ≫ rightCoactionPow G R (n + 1) X := by
  induction n generalizing X with
  | zero =>
    have hδ : deltaAtPos G 1 ⟨0, by omega⟩ X = G.δ.app X := rfl
    have hρ : rightCoactionPow G R 1 X =
        R.coaction.app (G.toFunctor.obj X) := rfl
    rw [hδ, hρ]
    exact R.coassoc_app X
  | succ n ih =>
    have hδ : deltaAtPos G (n + 2) ⟨n + 1, by omega⟩ X =
        deltaAtPos G (n + 1) ⟨n, by omega⟩ (G.toFunctor.obj X) := rfl
    have hρ : rightCoactionPow G R (n + 2) X =
        rightCoactionPow G R (n + 1) (G.toFunctor.obj X) := rfl
    have hρn : rightCoactionPow G R (n + 1) X =
        rightCoactionPow G R n (G.toFunctor.obj X) := rfl
    rw [hδ, hρ, hρn]
    exact ih (G.toFunctor.obj X)

/-- The right-coaction counit identity at the outer contraction.

The iterated right coaction followed by counit contraction at the outermost left-end position
is the identity. -/
theorem rightCoactionPow_counit_last (n : ℕ) (X : C) :
    rightCoactionPow G R n X ≫
      R.functor.map (epsilonAtPos G n ⟨n, by omega⟩ X) = 𝟙 _ := by
  induction n generalizing X with
  | zero =>
    have hε : epsilonAtPos G 0 ⟨0, by omega⟩ X = G.ε.app X := rfl
    have hρ : rightCoactionPow G R 0 X = R.coaction.app X := rfl
    rw [hε, hρ]
    exact R.counit_app X
  | succ n ih =>
    have hε : epsilonAtPos G (n + 1) ⟨n + 1, by omega⟩ X =
        epsilonAtPos G n ⟨n, by omega⟩ (G.toFunctor.obj X) := rfl
    have hρ : rightCoactionPow G R (n + 1) X =
        rightCoactionPow G R n (G.toFunctor.obj X) := rfl
    rw [hε, hρ]
    exact ih (G.toFunctor.obj X)

/-- Interchange of right coaction and an interior comultiplication.

The right coaction followed by comultiplication at a surviving insertion position equals that
comultiplication followed by the next iterated right coaction. -/
theorem rightCoactionPow_delta_castSucc (n : ℕ) (k : Fin n) (X : C) :
    rightCoactionPow G R n X ≫
      R.functor.map (deltaAtPos G (n + 1) k.castSucc X) =
    R.functor.map (deltaAtPos G n k X) ≫
      rightCoactionPow G R (n + 1) X := by
  induction n generalizing X with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    match k with
    | ⟨0, hi⟩ =>
      have hcast0 : (Fin.castSucc (⟨0, hi⟩ : Fin (n + 1)) :
          Fin (n + 2)) = ⟨0, by omega⟩ := by
        apply Fin.ext; simp
      -- explicit change for the castSucc position, elaboration does not
      -- unfold it automatically
      change rightCoactionPow G R (n + 1) X ≫
          R.functor.map (deltaAtPos G (n + 2)
            (Fin.castSucc (⟨0, hi⟩ : Fin (n + 1))) X) =
        R.functor.map (deltaAtPos G (n + 1) (⟨0, hi⟩ : Fin (n + 1)) X) ≫
          rightCoactionPow G R (n + 2) X
      rw [hcast0]
      -- make definitional coaction successors explicit
      change rightCoactionPow G R (n + 1) X ≫
          R.functor.map ((comonadPow G (n + 1)).map (G.δ.app X)) =
        R.functor.map ((comonadPow G n).map (G.δ.app X)) ≫
          rightCoactionPow G R (n + 2) X
      have hρn : rightCoactionPow G R (n + 1) X =
          rightCoactionPow G R n (G.toFunctor.obj X) := rfl
      have hρS : rightCoactionPow G R (n + 2) X =
          rightCoactionPow G R (n + 1) (G.toFunctor.obj X) := rfl
      rw [hρn, hρS]
      -- unfold once more for the raw zero naturality; use the functor-comp
      -- object form that appears in G.δ.app X's codomain to match
      -- naturality's binder
      change rightCoactionPow G R n (G.toFunctor.obj X) ≫
          R.functor.map ((comonadPow G (n + 1)).map (G.δ.app X)) =
        R.functor.map ((comonadPow G n).map (G.δ.app X)) ≫
          rightCoactionPow G R n ((G.toFunctor ⋙ G.toFunctor).obj X)
      -- raw position-zero case via rightCoactionPow_naturality
      exact (rightCoactionPow_naturality G R n (f := G.δ.app X)).symm
    | ⟨k + 1, hk⟩ =>
      let k0 : Fin n := ⟨k, by omega⟩
      have hcast_succ : (Fin.castSucc (⟨k + 1, hk⟩ : Fin (n + 1)) :
          Fin (n + 2)) = (Fin.castSucc k0).succ := by
        apply Fin.ext; simp [k0]
      have hδ_cast : deltaAtPos G (n + 2)
          (Fin.castSucc (⟨k + 1, hk⟩ : Fin (n + 1))) X =
          deltaAtPos G (n + 1) (Fin.castSucc k0)
            (G.toFunctor.obj X) := by
        rw [hcast_succ]; rfl
      have hδ_k : deltaAtPos G (n + 1) (⟨k + 1, hk⟩ : Fin (n + 1)) X =
          deltaAtPos G n k0 (G.toFunctor.obj X) := rfl
      have hρn : rightCoactionPow G R (n + 1) X =
          rightCoactionPow G R n (G.toFunctor.obj X) := rfl
      have hρS : rightCoactionPow G R (n + 2) X =
          rightCoactionPow G R (n + 1) (G.toFunctor.obj X) := rfl
      -- explicit change where elaboration keeps the raw succ equations folded
      change rightCoactionPow G R (n + 1) X ≫
          R.functor.map (deltaAtPos G (n + 2)
            (Fin.castSucc (⟨k + 1, hk⟩ : Fin (n + 1))) X) =
        R.functor.map (deltaAtPos G (n + 1) (⟨k + 1, hk⟩ : Fin (n + 1)) X) ≫
          rightCoactionPow G R (n + 2) X
      rw [hδ_cast, hδ_k, hρn, hρS]
      exact ih k0 (G.toFunctor.obj X)

/-- The left-coaction coassociativity identity at the innermost insertion.

The mapped left coaction followed by innermost comultiplication equals the two successive left
coactions mapped through `G^n` and `R`. -/
theorem leftCoaction_delta_zero (n : ℕ) (a : A) :
    R.functor.map ((comonadPow G n).map (L.coaction.app a)) ≫
      R.functor.map (deltaAtPos G (n + 1) ⟨0, by omega⟩
        (L.functor.obj a)) =
    R.functor.map ((comonadPow G n).map (L.coaction.app a)) ≫
      R.functor.map ((comonadPow G n).map
        (G.toFunctor.map (L.coaction.app a))) := by
  have hδ : deltaAtPos G (n + 1) ⟨0, by omega⟩ (L.functor.obj a) =
      (comonadPow G n).map (G.δ.app (L.functor.obj a)) := rfl
  have hL := L.coassoc_app a
  rw [hδ, ← R.functor.map_comp, ← R.functor.map_comp,
    ← (comonadPow G n).map_comp, ← (comonadPow G n).map_comp, hL]

/-- The left-coaction counit identity at the innermost contraction.

The mapped left coaction followed by innermost counit contraction is the identity on the cobar
degree. -/
theorem leftCoaction_epsilon_zero (n : ℕ) (a : A) :
    R.functor.map ((comonadPow G n).map (L.coaction.app a)) ≫
      R.functor.map (epsilonAtPos G n ⟨0, by omega⟩
        (L.functor.obj a)) = 𝟙 _ := by
  have hε : epsilonAtPos G n ⟨0, by omega⟩ (L.functor.obj a) =
      (comonadPow G n).map (G.ε.app (L.functor.obj a)) := by
    cases n with
    | zero => rfl
    | succ m => rfl
  have hL := L.counit_app a
  rw [hε, ← R.functor.map_comp, ← (comonadPow G n).map_comp, hL,
    (comonadPow G n).map_id, R.functor.map_id]

/-- Naturality of comultiplication insertion along a left coaction.

Applying a power of the left coaction commutes with the insertion maps at `L(a)` and
`G(L(a))`. -/
theorem leftCoaction_delta_naturality (n : ℕ) (k : Fin n) (a : A) :
    (comonadPow G n).map (L.coaction.app a) ≫
      deltaAtPos G n k (G.toFunctor.obj (L.functor.obj a)) =
    deltaAtPos G n k (L.functor.obj a) ≫
      (comonadPow G (n + 1)).map (L.coaction.app a) :=
  deltaAtPos_naturality G n k (L.coaction.app a)

/-- Naturality of counit insertion along a left coaction.

Applying a power of the left coaction commutes with the counit contraction maps at `L(a)` and
`G(L(a))`. -/
theorem leftCoaction_epsilon_naturality (n : ℕ) (i : Fin (n + 1)) (a : A) :
    (comonadPow G (n + 1)).map (L.coaction.app a) ≫
      epsilonAtPos G n i (G.toFunctor.obj (L.functor.obj a)) =
    epsilonAtPos G n i (L.functor.obj a) ≫
      (comonadPow G n).map (L.coaction.app a) :=
  epsilonAtPos_naturality G n i (L.coaction.app a)

end CoactionCalculus

section CofaceCoface

variable {G : Comonad C} {R : RightComodule G D} {L : LeftComodule A G}

/-- The componentwise cobar coface identity.

For `i ≤ j`, the component composites satisfy `δ_n^i ≫ δ_(n+1)^(j+1) = δ_n^j ≫ δ_(n+1)^i` at
every object `a`. -/
theorem cobarCofaceApp_coface_coface (n : ℕ) (i j : Fin (n + 2)) (hij : i ≤ j)
    (a : A) :
    cobarCofaceApp (G := G) (R := R) (L := L) n i a ≫
      cobarCofaceApp (G := G) (R := R) (L := L) (n + 1) j.succ a =
    cobarCofaceApp (G := G) (R := R) (L := L) n j a ≫
      cobarCofaceApp (G := G) (R := R) (L := L) (n + 1) i.castSucc a := by
  have hij_val : i.val ≤ j.val := Fin.le_def.mp hij
  by_cases hi0 : i.val = 0
  · have h_i_right : cobarCofaceApp (G := G) (R := R) (L := L) n i a =
        rightCoactionPow G R n (L.functor.obj a) :=
      cobarCofaceApp_of_val_zero (G := G) (R := R) (L := L) hi0
    have h_i_cast_val : (Fin.castSucc i : Fin (n + 3)).val = i.val := rfl
    have h_i_cast_zero : (Fin.castSucc i : Fin (n + 3)).val = 0 := by
      rw [h_i_cast_val, hi0]
    have h_i_cast_right :
        cobarCofaceApp (G := G) (R := R) (L := L) (n + 1) i.castSucc a =
        rightCoactionPow G R (n + 1) (L.functor.obj a) :=
      cobarCofaceApp_of_val_zero (G := G) (R := R) (L := L) h_i_cast_zero
    by_cases hj0 : j.val = 0
    · have h_j_right : cobarCofaceApp (G := G) (R := R) (L := L) n j a =
          rightCoactionPow G R n (L.functor.obj a) :=
        cobarCofaceApp_of_val_zero (G := G) (R := R) (L := L) hj0
      have h_j_succ_val : (Fin.succ j : Fin (n + 3)).val = j.val + 1 := rfl
      have h_jsucc_eq : (Fin.succ j : Fin (n + 3)).val =
          (⟨0, by omega⟩ : Fin (n + 1)).val + 1 := by
        rw [h_j_succ_val, hj0]
      have h_jsucc_mid :
          cobarCofaceApp (G := G) (R := R) (L := L) (n + 1) j.succ a =
          R.functor.map
            (cobarDeltaAtPos G (n + 1) ⟨0, by omega⟩ (L.functor.obj a)) :=
        cobarCofaceApp_of_middle (G := G) (R := R) (L := L)
          (k := ⟨0, by omega⟩) h_jsucc_eq
      rw [h_jsucc_mid, h_i_right, h_i_cast_right, h_j_right]
      have h_cobar : cobarDeltaAtPos G (n + 1) ⟨0, by omega⟩
          (L.functor.obj a) =
          deltaAtPos G (n + 1) ⟨n, by omega⟩ (L.functor.obj a) := by
        simp only [cobarDeltaAtPos]
        have : (⟨0, by omega⟩ : Fin (n + 1)).rev = ⟨n, by omega⟩ := by
          apply Fin.ext
          simp [Fin.rev]
        rw [this]
      rw [h_cobar]
      exact rightCoactionPow_coassoc_last (G := G) (R := R) n
        (L.functor.obj a)
    · by_cases hjLast : j.val = n + 1
      · have h_j_left : cobarCofaceApp (G := G) (R := R) (L := L) n j a =
            R.functor.map ((comonadPow G n).map (L.coaction.app a)) :=
          cobarCofaceApp_of_val_last (G := G) (R := R) (L := L) hjLast
        have h_j_succ_val : (Fin.succ j : Fin (n + 3)).val = j.val + 1 := rfl
        have h_jsucc_last : (Fin.succ j : Fin (n + 3)).val = (n + 1) + 1 := by
          rw [h_j_succ_val, hjLast]
        have h_jsucc_left :
            cobarCofaceApp (G := G) (R := R) (L := L) (n + 1) j.succ a =
            R.functor.map ((comonadPow G (n + 1)).map (L.coaction.app a)) :=
          cobarCofaceApp_of_val_last (G := G) (R := R) (L := L) h_jsucc_last
        rw [h_jsucc_left, h_i_right, h_i_cast_right, h_j_left]
        have hρ : rightCoactionPow G R (n + 1) (L.functor.obj a) =
            rightCoactionPow G R n
              (G.toFunctor.obj (L.functor.obj a)) := rfl
        rw [hρ]
        exact (rightCoactionPow_naturality G R n (L.coaction.app a)).symm
      · have hj_pos : 0 < j.val := by omega
        have hj_le : j.val ≤ n := by omega
        let j0 : Fin n := ⟨j.val - 1, by omega⟩
        have hj_eq : j.val = j0.val + 1 := by
          have h1 : 1 ≤ j.val := by omega
          have h2 : j.val - 1 + 1 = j.val := Nat.sub_add_cancel h1
          have hjv : j0.val = j.val - 1 := rfl
          rw [← hjv] at h2
          exact h2.symm
        let kUpper : Fin (n + 1) := ⟨j.val, by omega⟩
        have h_j_mid : cobarCofaceApp (G := G) (R := R) (L := L) n j a =
            R.functor.map
              (cobarDeltaAtPos G n j0 (L.functor.obj a)) :=
          cobarCofaceApp_of_middle (G := G) (R := R) (L := L) (k := j0)
            (by rw [hj_eq])
        have h_j_succ_val : (Fin.succ j : Fin (n + 3)).val = j.val + 1 := rfl
        have h_jsucc_eq : (Fin.succ j : Fin (n + 3)).val = kUpper.val + 1 := by
          have : kUpper.val = j.val := rfl
          rw [h_j_succ_val, this]
        have h_jsucc_mid :
            cobarCofaceApp (G := G) (R := R) (L := L) (n + 1) j.succ a =
            R.functor.map
              (cobarDeltaAtPos G (n + 1) kUpper (L.functor.obj a)) :=
          cobarCofaceApp_of_middle (G := G) (R := R) (L := L) (k := kUpper)
            h_jsucc_eq
        have h_j0_succ_eq : kUpper = j0.succ := by
          apply Fin.ext
          have hk : kUpper.val = j.val := rfl
          have hs : j0.succ.val = j0.val + 1 := rfl
          rw [hk, hs, hj_eq]
        rw [h_j0_succ_eq] at h_jsucc_mid
        rw [h_jsucc_mid, h_i_right, h_i_cast_right, h_j_mid]
        have h_raw_j0 : cobarDeltaAtPos G n j0 (L.functor.obj a) =
            deltaAtPos G n j0.rev (L.functor.obj a) := rfl
        have h_raw_succ : cobarDeltaAtPos G (n + 1) j0.succ
            (L.functor.obj a) =
            deltaAtPos G (n + 1) j0.succ.rev (L.functor.obj a) := rfl
        have h_rev : j0.succ.rev = (j0.rev).castSucc := Fin.rev_succ j0
        rw [h_raw_j0, h_raw_succ, h_rev]
        exact rightCoactionPow_delta_castSucc (G := G) (R := R) n j0.rev
          (L.functor.obj a)
  · by_cases hiLast : i.val = n + 1
    · have hjLast : j.val = n + 1 := by omega
      have h_i_left : cobarCofaceApp (G := G) (R := R) (L := L) n i a =
          R.functor.map ((comonadPow G n).map (L.coaction.app a)) :=
        cobarCofaceApp_of_val_last (G := G) (R := R) (L := L) hiLast
      have h_j_left : cobarCofaceApp (G := G) (R := R) (L := L) n j a =
          R.functor.map ((comonadPow G n).map (L.coaction.app a)) :=
        cobarCofaceApp_of_val_last (G := G) (R := R) (L := L) hjLast
      have h_i_cast_val : (Fin.castSucc i : Fin (n + 3)).val = i.val := rfl
      have h_j_succ_val : (Fin.succ j : Fin (n + 3)).val = j.val + 1 := rfl
      have h_i_cast_eq : (Fin.castSucc i : Fin (n + 3)).val =
          (⟨n, by omega⟩ : Fin (n + 1)).val + 1 := by
        rw [h_i_cast_val, hiLast]
      have h_jsucc_last : (Fin.succ j : Fin (n + 3)).val = (n + 1) + 1 := by
        rw [h_j_succ_val, hjLast]
      have h_i_cast_mid :
          cobarCofaceApp (G := G) (R := R) (L := L) (n + 1) i.castSucc a =
          R.functor.map
            (cobarDeltaAtPos G (n + 1) ⟨n, by omega⟩ (L.functor.obj a)) := by
        exact cobarCofaceApp_of_middle (G := G) (R := R) (L := L)
          (k := ⟨n, by omega⟩) h_i_cast_eq
      have h_jsucc_left :
          cobarCofaceApp (G := G) (R := R) (L := L) (n + 1) j.succ a =
          R.functor.map ((comonadPow G (n + 1)).map (L.coaction.app a)) := by
        exact cobarCofaceApp_of_val_last (G := G) (R := R) (L := L)
          h_jsucc_last
      have h_cobar : cobarDeltaAtPos G (n + 1) ⟨n, by omega⟩
          (L.functor.obj a) =
          deltaAtPos G (n + 1) ⟨0, by omega⟩ (L.functor.obj a) := by
        simp only [cobarDeltaAtPos]
        have : (⟨n, by omega⟩ : Fin (n + 1)).rev = ⟨0, by omega⟩ := by
          apply Fin.ext
          simp [Fin.rev]
        rw [this]
      have hY : (comonadPow G (n + 1)).map (L.coaction.app a) =
          (comonadPow G n).map
            (G.toFunctor.map (L.coaction.app a)) := rfl
      calc cobarCofaceApp (G := G) (R := R) (L := L) n i a ≫
              cobarCofaceApp (G := G) (R := R) (L := L) (n + 1) j.succ a
          = R.functor.map ((comonadPow G n).map (L.coaction.app a)) ≫
            R.functor.map ((comonadPow G (n + 1)).map (L.coaction.app a)) := by
            rw [h_jsucc_left, h_i_left]
        _ = R.functor.map ((comonadPow G n).map (L.coaction.app a)) ≫
            R.functor.map (deltaAtPos G (n + 1) ⟨0, by omega⟩
              (L.functor.obj a)) := by
            rw [hY]
            exact (leftCoaction_delta_zero (G := G) (R := R) (L := L) n a).symm
        _ = R.functor.map ((comonadPow G n).map (L.coaction.app a)) ≫
            R.functor.map ((comonadPow G n).map
              (G.toFunctor.map (L.coaction.app a))) := by
            rw [leftCoaction_delta_zero (G := G) (R := R) (L := L) n a]
        _ = cobarCofaceApp (G := G) (R := R) (L := L) n j a ≫
              cobarCofaceApp (G := G) (R := R) (L := L)
                (n + 1) i.castSucc a := by
            rw [h_j_left, h_i_cast_mid, h_cobar]
            exact (leftCoaction_delta_zero (G := G) (R := R) (L := L) n a).symm
    · have hi_pos : 0 < i.val := by omega
      have hi_le : i.val ≤ n := by omega
      by_cases hjLast : j.val = n + 1
      · let i0 : Fin n := ⟨i.val - 1, by omega⟩
        have hi_eq : i.val = i0.val + 1 := by
          have h1 : 1 ≤ i.val := by omega
          have h2 : i.val - 1 + 1 = i.val := Nat.sub_add_cancel h1
          have hi0v : i0.val = i.val - 1 := rfl
          rw [← hi0v] at h2
          exact h2.symm
        have h_i_mid : cobarCofaceApp (G := G) (R := R) (L := L) n i a =
            R.functor.map
              (cobarDeltaAtPos G n i0 (L.functor.obj a)) :=
          cobarCofaceApp_of_middle (G := G) (R := R) (L := L) (k := i0)
            (by rw [hi_eq])
        have h_j_left : cobarCofaceApp (G := G) (R := R) (L := L) n j a =
            R.functor.map ((comonadPow G n).map (L.coaction.app a)) :=
          cobarCofaceApp_of_val_last (G := G) (R := R) (L := L) hjLast
        have h_j_succ_val : (Fin.succ j : Fin (n + 3)).val = j.val + 1 := rfl
        have h_jsucc_last : (Fin.succ j : Fin (n + 3)).val = (n + 1) + 1 := by
          rw [h_j_succ_val, hjLast]
        have h_jsucc_left :
            cobarCofaceApp (G := G) (R := R) (L := L) (n + 1) j.succ a =
            R.functor.map ((comonadPow G (n + 1)).map (L.coaction.app a)) :=
          cobarCofaceApp_of_val_last (G := G) (R := R) (L := L) h_jsucc_last
        have h_i_cast_val : (Fin.castSucc i : Fin (n + 3)).val = i.val := rfl
        let i0c : Fin (n + 1) := i0.castSucc
        have hi0c_val : i0c.val = i0.val := rfl
        have h_i_cast_eq : (Fin.castSucc i : Fin (n + 3)).val =
            i0c.val + 1 := by
          rw [h_i_cast_val, hi0c_val, hi_eq]
        have h_i_cast_mid :
            cobarCofaceApp (G := G) (R := R) (L := L) (n + 1) i.castSucc a =
            R.functor.map
              (cobarDeltaAtPos G (n + 1) i0c (L.functor.obj a)) := by
          exact cobarCofaceApp_of_middle (G := G) (R := R) (L := L)
            (k := i0c) h_i_cast_eq
        rw [h_jsucc_left, h_i_mid, h_i_cast_mid, h_j_left]
        have h_raw_i0 : cobarDeltaAtPos G n i0 (L.functor.obj a) =
            deltaAtPos G n i0.rev (L.functor.obj a) := rfl
        have h_raw_i0c : cobarDeltaAtPos G (n + 1) i0c (L.functor.obj a) =
            deltaAtPos G (n + 1) i0c.rev (L.functor.obj a) := rfl
        have h_rev : i0c.rev = (i0.rev).succ := Fin.rev_castSucc i0
        rw [h_raw_i0, h_raw_i0c, h_rev]
        have hδS : deltaAtPos G (n + 1) (i0.rev).succ (L.functor.obj a) =
            deltaAtPos G n i0.rev
              (G.toFunctor.obj (L.functor.obj a)) := rfl
        have hY : (comonadPow G (n + 1)).map (L.coaction.app a) =
            (comonadPow G n).map
              (G.toFunctor.map (L.coaction.app a)) := rfl
        calc R.functor.map (deltaAtPos G n i0.rev (L.functor.obj a)) ≫
                R.functor.map ((comonadPow G (n + 1)).map (L.coaction.app a))
            = R.functor.map (deltaAtPos G n i0.rev (L.functor.obj a)) ≫
              R.functor.map ((comonadPow G n).map
                (G.toFunctor.map (L.coaction.app a))) := by
              rw [hY]
          _ = R.functor.map ((comonadPow G n).map (L.coaction.app a)) ≫
              R.functor.map (deltaAtPos G n i0.rev
                (G.toFunctor.obj (L.functor.obj a))) := by
              rw [← R.functor.map_comp, ← R.functor.map_comp]
              have hnat := leftCoaction_delta_naturality (G := G) (L := L)
                n i0.rev a
              rw [hnat, hY]
          _ = R.functor.map ((comonadPow G n).map (L.coaction.app a)) ≫
              R.functor.map (deltaAtPos G (n + 1) (i0.rev).succ
                (L.functor.obj a)) := by
              rw [hδS]
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
          exact Fin.le_def.mpr this
        have h_i_mid : cobarCofaceApp (G := G) (R := R) (L := L) n i a =
            R.functor.map
              (cobarDeltaAtPos G n i0 (L.functor.obj a)) :=
          cobarCofaceApp_of_middle (G := G) (R := R) (L := L) (k := i0)
            (by rw [hi_eq])
        have h_j_mid : cobarCofaceApp (G := G) (R := R) (L := L) n j a =
            R.functor.map
              (cobarDeltaAtPos G n j0 (L.functor.obj a)) :=
          cobarCofaceApp_of_middle (G := G) (R := R) (L := L) (k := j0)
            (by rw [hj_eq])
        have h_i_cast_val : (Fin.castSucc i : Fin (n + 3)).val = i.val := rfl
        have h_j_succ_val : (Fin.succ j : Fin (n + 3)).val = j.val + 1 := rfl
        let i0c : Fin (n + 1) := i0.castSucc
        let j0s : Fin (n + 1) := j0.succ
        have hi0c_val : i0c.val = i0.val := rfl
        have hj0s_val : j0s.val = j0.val + 1 := rfl
        have h_i_cast_eq : (Fin.castSucc i : Fin (n + 3)).val =
            i0c.val + 1 := by
          rw [h_i_cast_val, hi0c_val, hi_eq]
        have h_j_succ_eq : (Fin.succ j : Fin (n + 3)).val = j0s.val + 1 := by
          rw [h_j_succ_val, hj0s_val, hj_eq]
        have h_i_cast_mid :
            cobarCofaceApp (G := G) (R := R) (L := L) (n + 1) i.castSucc a =
            R.functor.map
              (cobarDeltaAtPos G (n + 1) i0c (L.functor.obj a)) :=
          cobarCofaceApp_of_middle (G := G) (R := R) (L := L) (k := i0c)
            h_i_cast_eq
        have h_j_succ_mid :
            cobarCofaceApp (G := G) (R := R) (L := L) (n + 1) j.succ a =
            R.functor.map
              (cobarDeltaAtPos G (n + 1) j0s (L.functor.obj a)) :=
          cobarCofaceApp_of_middle (G := G) (R := R) (L := L) (k := j0s)
            h_j_succ_eq
        rw [h_j_succ_mid, h_i_mid, h_i_cast_mid, h_j_mid]
        have h_raw_i0 : cobarDeltaAtPos G n i0 (L.functor.obj a) =
            deltaAtPos G n i0.rev (L.functor.obj a) := rfl
        have h_raw_j0 : cobarDeltaAtPos G n j0 (L.functor.obj a) =
            deltaAtPos G n j0.rev (L.functor.obj a) := rfl
        have h_raw_i0c : cobarDeltaAtPos G (n + 1) i0c (L.functor.obj a) =
            deltaAtPos G (n + 1) i0c.rev (L.functor.obj a) := rfl
        have h_raw_j0s : cobarDeltaAtPos G (n + 1) j0s (L.functor.obj a) =
            deltaAtPos G (n + 1) j0s.rev (L.functor.obj a) := rfl
        have h_rc : i0c.rev = (i0.rev).succ := Fin.rev_castSucc i0
        have h_rs : j0s.rev = (j0.rev).castSucc := Fin.rev_succ j0
        rw [h_raw_i0, h_raw_j0, h_raw_i0c, h_raw_j0s, h_rc, h_rs]
        have h_le_rev : j0.rev ≤ i0.rev := by
          rwa [Fin.rev_le_rev]
        have h_δ := deltaAtPos_face_face (G := G) n j0.rev i0.rev h_le_rev
          (L.functor.obj a)
        calc R.functor.map (deltaAtPos G n i0.rev (L.functor.obj a)) ≫
                R.functor.map
                  (deltaAtPos G (n + 1) (j0.rev).castSucc
                    (L.functor.obj a))
            = R.functor.map (deltaAtPos G n i0.rev (L.functor.obj a) ≫
                  deltaAtPos G (n + 1) (j0.rev).castSucc
                    (L.functor.obj a)) := by
              rw [← R.functor.map_comp]
          _ = R.functor.map (deltaAtPos G n j0.rev (L.functor.obj a) ≫
                  deltaAtPos G (n + 1) (i0.rev).succ
                    (L.functor.obj a)) := by
              rw [h_δ.symm]
          _ = R.functor.map (deltaAtPos G n j0.rev (L.functor.obj a)) ≫
                R.functor.map
                  (deltaAtPos G (n + 1) (i0.rev).succ
                    (L.functor.obj a)) := by
              rw [R.functor.map_comp]

/-- The natural-transformation cobar coface identity.

For `i ≤ j`, the cofaces satisfy `δ_n^i ≫ δ_(n+1)^(j+1) = δ_n^j ≫ δ_(n+1)^i`. -/
theorem cobarCoface_coface_coface (n : ℕ) (i j : Fin (n + 2)) (hij : i ≤ j) :
    cobarCoface (G := G) (R := R) (L := L) n i ≫
      cobarCoface (G := G) (R := R) (L := L) (n + 1) j.succ =
    cobarCoface (G := G) (R := R) (L := L) n j ≫
      cobarCoface (G := G) (R := R) (L := L) (n + 1) i.castSucc := by
  ext a
  exact cobarCofaceApp_coface_coface (G := G) (R := R) (L := L) n i j hij a

end CofaceCoface

section CodegCodeg

variable {G : Comonad C} {R : RightComodule G D} {L : LeftComodule A G}

/-- The componentwise cobar codegeneracy identity.

For `i ≤ j`, the component composites satisfy `σ_(n+1)^i ≫ σ_n^j = σ_(n+1)^(j+1) ≫ σ_n^i` at
every object. -/
theorem cobarCodegeneracyApp_deg_deg (n : ℕ) (i j : Fin (n + 1)) (hij : i ≤ j)
    (a : A) :
    (cobarCodegeneracy (G := G) (R := R) (L := L) (n + 1) i.castSucc).app a ≫
      (cobarCodegeneracy (G := G) (R := R) (L := L) n j).app a =
    (cobarCodegeneracy (G := G) (R := R) (L := L) (n + 1) j.succ).app a ≫
      (cobarCodegeneracy (G := G) (R := R) (L := L) n i).app a := by
  have h_le_rev : j.rev ≤ i.rev := by
    rwa [Fin.rev_le_rev]
  have hraw := epsilonAtPos_deg_deg G n j.rev i.rev h_le_rev
    (L.functor.obj a)
  have h1 : (Fin.castSucc i : Fin (n + 2)).rev = (i.rev).succ :=
    Fin.rev_castSucc i
  have h2 : (Fin.succ j : Fin (n + 2)).rev = (j.rev).castSucc :=
    Fin.rev_succ j
  simp only [cobarCodegeneracy_app, cobarEpsilonAtPos_rev]
  rw [h1, h2, ← R.functor.map_comp, ← R.functor.map_comp, hraw.symm]

/-- The natural-transformation cobar codegeneracy identity.

For `i ≤ j`, the codegeneracies satisfy `σ_(n+1)^i ≫ σ_n^j = σ_(n+1)^(j+1) ≫ σ_n^i`. -/
theorem cobarCodegeneracy_deg_deg (n : ℕ) (i j : Fin (n + 1)) (hij : i ≤ j) :
    cobarCodegeneracy (G := G) (R := R) (L := L) (n + 1) i.castSucc ≫
      cobarCodegeneracy (G := G) (R := R) (L := L) n j =
    cobarCodegeneracy (G := G) (R := R) (L := L) (n + 1) j.succ ≫
      cobarCodegeneracy (G := G) (R := R) (L := L) n i := by
  ext a
  exact cobarCodegeneracyApp_deg_deg (G := G) (R := R) (L := L) n i j hij a

end CodegCodeg

section RightCoactionEpsilon

variable {G : Comonad C} {R : RightComodule G D}

/-- Interchange of right coaction and an interior counit contraction.

The next-degree right coaction followed by a surviving counit contraction equals that
contraction one degree lower followed by the preceding right coaction. -/
theorem rightCoactionPow_epsilon_castSucc (n : ℕ) (i : Fin (n + 1)) (X : C) :
    rightCoactionPow G R (n + 1) X ≫
      R.functor.map (epsilonAtPos G (n + 1) i.castSucc X) =
    R.functor.map (epsilonAtPos G n i X) ≫ rightCoactionPow G R n X := by
  induction n generalizing X with
  | zero =>
    have hi : i = ⟨0, by omega⟩ := by
      have : i.val = 0 := by omega
      ext; exact this
    subst hi
    change rightCoactionPow G R 1 X ≫
        R.functor.map (epsilonAtPos G 1
          (Fin.castSucc (⟨0, by omega⟩ : Fin 1)) X) =
      R.functor.map (epsilonAtPos G 0 (⟨0, by omega⟩ : Fin 1) X) ≫
        rightCoactionPow G R 0 X
    have hcast : (Fin.castSucc (⟨0, by omega⟩ : Fin 1) : Fin 2) =
        ⟨0, by omega⟩ := by
      apply Fin.ext; simp
    rw [hcast]
    change rightCoactionPow G R 1 X ≫
        R.functor.map ((comonadPow G 1).map (G.ε.app X)) =
      R.functor.map (G.ε.app X) ≫ rightCoactionPow G R 0 X
    have hρ0 : rightCoactionPow G R 0 X = R.coaction.app X := rfl
    have hρ1 : rightCoactionPow G R 1 X =
        R.coaction.app (G.toFunctor.obj X) := rfl
    rw [hρ0, hρ1]
    change R.coaction.app (G.toFunctor.obj X) ≫
        R.functor.map (G.toFunctor.map (G.ε.app X)) =
      R.functor.map (G.ε.app X) ≫ R.coaction.app X
    exact (R.coaction.naturality (G.ε.app X)).symm
  | succ n ih =>
    match i with
    | ⟨0, hi⟩ =>
      have hcast0 : (Fin.castSucc (⟨0, hi⟩ : Fin (n + 2)) :
          Fin (n + 3)) = ⟨0, by omega⟩ := by
        apply Fin.ext; simp
      change rightCoactionPow G R (n + 2) X ≫
          R.functor.map (epsilonAtPos G (n + 2)
            (Fin.castSucc (⟨0, hi⟩ : Fin (n + 2))) X) =
        R.functor.map (epsilonAtPos G (n + 1)
          (⟨0, hi⟩ : Fin (n + 2)) X) ≫
          rightCoactionPow G R (n + 1) X
      rw [hcast0]
      change rightCoactionPow G R (n + 2) X ≫
          R.functor.map ((comonadPow G (n + 2)).map (G.ε.app X)) =
        R.functor.map ((comonadPow G (n + 1)).map (G.ε.app X)) ≫
          rightCoactionPow G R (n + 1) X
      have hr1 : rightCoactionPow G R (n + 1) X =
          rightCoactionPow G R n (G.toFunctor.obj X) := rfl
      have hr2 : rightCoactionPow G R (n + 2) X =
          rightCoactionPow G R (n + 1) (G.toFunctor.obj X) := rfl
      rw [hr1, hr2]
      change rightCoactionPow G R (n + 1) (G.toFunctor.obj X) ≫
          R.functor.map ((comonadPow G (n + 2)).map (G.ε.app X)) =
        R.functor.map ((comonadPow G (n + 1)).map (G.ε.app X)) ≫
          rightCoactionPow G R n (G.toFunctor.obj X)
      exact (rightCoactionPow_naturality G R (n + 1) (f := G.ε.app X)).symm
    | ⟨k + 1, hk⟩ =>
      let i0 : Fin (n + 1) := ⟨k, by omega⟩
      have hcast_succ : (Fin.castSucc (⟨k + 1, hk⟩ : Fin (n + 2)) :
          Fin (n + 3)) = (Fin.castSucc i0).succ := by
        apply Fin.ext; simp [i0]
      have hε_cast : epsilonAtPos G (n + 2)
          (Fin.castSucc (⟨k + 1, hk⟩ : Fin (n + 2))) X =
          epsilonAtPos G (n + 1) (Fin.castSucc i0)
            (G.toFunctor.obj X) := by
        rw [hcast_succ]; rfl
      have hε_i : epsilonAtPos G (n + 1) (⟨k + 1, hk⟩ : Fin (n + 2)) X =
          epsilonAtPos G n i0 (G.toFunctor.obj X) := rfl
      have hr1 : rightCoactionPow G R (n + 1) X =
          rightCoactionPow G R n (G.toFunctor.obj X) := rfl
      have hr2 : rightCoactionPow G R (n + 2) X =
          rightCoactionPow G R (n + 1) (G.toFunctor.obj X) := rfl
      change rightCoactionPow G R (n + 2) X ≫
          R.functor.map (epsilonAtPos G (n + 2)
            (Fin.castSucc (⟨k + 1, hk⟩ : Fin (n + 2))) X) =
        R.functor.map (epsilonAtPos G (n + 1)
          (⟨k + 1, hk⟩ : Fin (n + 2)) X) ≫
          rightCoactionPow G R (n + 1) X
      rw [hε_cast, hε_i, hr1, hr2]
      have h_eq : rightCoactionPow G R (n + 1) (G.toFunctor.obj X) ≫
          R.functor.map (epsilonAtPos G (n + 1) (Fin.castSucc i0)
            (G.toFunctor.obj X)) =
        R.functor.map (epsilonAtPos G n i0 (G.toFunctor.obj X)) ≫
          rightCoactionPow G R n (G.toFunctor.obj X) :=
        ih i0 (G.toFunctor.obj X)
      change rightCoactionPow G R (n + 1) (G.toFunctor.obj X) ≫
          R.functor.map (epsilonAtPos G (n + 1) (Fin.castSucc i0)
            (G.toFunctor.obj X)) =
        R.functor.map (epsilonAtPos G n i0 (G.toFunctor.obj X)) ≫
          rightCoactionPow G R n (G.toFunctor.obj X)
      exact h_eq

end RightCoactionEpsilon

section DeltaEpsilonDistant

variable (G : Comonad C)

/-- The mixed insertion identity with counit before comultiplication.

For left-end positions `j ≤ i`, comultiplication at `i.succ` followed by counit at
`j.castSucc` equals counit at `j` followed by comultiplication at `i`. -/
theorem deltaAtPos_epsilonAtPos_succ_castSucc_of_le (n : ℕ) (i : Fin n)
    (j : Fin (n + 1)) (h : j.val ≤ i.val) (X : C) :
    deltaAtPos G (n + 1) i.succ X ≫ epsilonAtPos G (n + 1) j.castSucc X =
      epsilonAtPos G n j X ≫ deltaAtPos G n i X := by
  induction n generalizing X with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    by_cases hj0 : j.val = 0
    · have hj_eq : j = ⟨0, by omega⟩ := by apply Fin.ext; omega
      have hj_cast_zero : (⟨0, by omega⟩ : Fin (n + 2)).castSucc =
          (⟨0, by omega⟩ : Fin (n + 3)) := by
        apply Fin.ext; simp
      have h_eps_zero : epsilonAtPos G (n + 2)
          (⟨0, by omega⟩ : Fin (n + 3)) X =
          (comonadPow G (n + 2)).map (G.ε.app X) := rfl
      have h_eps_zero' : epsilonAtPos G (n + 1)
          (⟨0, by omega⟩ : Fin (n + 2)) X =
          (comonadPow G (n + 1)).map (G.ε.app X) := rfl
      have h_δ_succ : deltaAtPos G (n + 2) i.succ X =
          deltaAtPos G (n + 1) i (G.toFunctor.obj X) := rfl
      calc deltaAtPos G (n + 2) i.succ X ≫ epsilonAtPos G (n + 2) j.castSucc X
          = deltaAtPos G (n + 1) i (G.toFunctor.obj X) ≫
            epsilonAtPos G (n + 2) (⟨0, by omega⟩ : Fin (n + 3)) X := by
            rw [hj_eq, hj_cast_zero, h_δ_succ]
      _ = deltaAtPos G (n + 1) i (G.toFunctor.obj X) ≫
            (comonadPow G (n + 2)).map (G.ε.app X) := by
            rw [h_eps_zero]
      _ = (comonadPow G (n + 1)).map (G.ε.app X) ≫
            deltaAtPos G (n + 1) i X := by
            have hnat := deltaAtPos_naturality G (n + 1) i (f := G.ε.app X)
            exact hnat.symm
      _ = epsilonAtPos G (n + 1) (⟨0, by omega⟩ : Fin (n + 2)) X ≫
            deltaAtPos G (n + 1) i X := by
            rw [h_eps_zero']
      _ = epsilonAtPos G (n + 1) j X ≫ deltaAtPos G (n + 1) i X := by
            rw [hj_eq]
    · have hj_pos : 0 < j.val := by omega
      have hj_sub : j.val - 1 < n + 1 := by omega
      let j0 : Fin (n + 1) := ⟨j.val - 1, hj_sub⟩
      have hj_eq : j = j0.succ := by
        apply Fin.ext
        simp [j0, Fin.succ]
        omega
      by_cases hi0 : i.val = 0
      · omega
      · have hi_pos : 0 < i.val := by omega
        have hi_sub : i.val - 1 < n := by omega
        let i0 : Fin n := ⟨i.val - 1, hi_sub⟩
        have hi_eq : i = i0.succ := by
          apply Fin.ext
          simp [i0, Fin.succ]
          omega
        have hj_le_i0 : j0.val ≤ i0.val := by
          have e1 : j0.val = j.val - 1 := rfl
          have e2 : i0.val = i.val - 1 := rfl
          omega
        have hj_cast_eq : j.castSucc = (j0.castSucc).succ := by
          apply Fin.ext
          simp [j0, Fin.castSucc, Fin.succ]
          omega
        have hi_succ_eq : i.succ = (i0.succ).succ := by
          apply Fin.ext
          simp [i0, Fin.succ]
          omega
        have h_ε_cast : epsilonAtPos G (n + 2) j.castSucc X =
            epsilonAtPos G (n + 1) j0.castSucc (G.toFunctor.obj X) := by
          rw [hj_cast_eq]
          rfl
        have h_δ_succ : deltaAtPos G (n + 2) i.succ X =
            deltaAtPos G (n + 1) i0.succ (G.toFunctor.obj X) := by
          rw [hi_succ_eq]
          rfl
        have h_δ : deltaAtPos G (n + 1) i X =
            deltaAtPos G n i0 (G.toFunctor.obj X) := by
          rw [hi_eq]
          rfl
        have h_ε : epsilonAtPos G (n + 1) j X =
            epsilonAtPos G n j0 (G.toFunctor.obj X) := by
          rw [hj_eq]
          rfl
        calc deltaAtPos G (n + 2) i.succ X ≫ epsilonAtPos G (n + 2) j.castSucc X
          = deltaAtPos G (n + 1) i0.succ (G.toFunctor.obj X) ≫
              epsilonAtPos G (n + 1) j0.castSucc (G.toFunctor.obj X) := by
                rw [h_δ_succ, h_ε_cast]
        _ = epsilonAtPos G n j0 (G.toFunctor.obj X) ≫
              deltaAtPos G n i0 (G.toFunctor.obj X) :=
                ih i0 j0 hj_le_i0 (G.toFunctor.obj X)
        _ = epsilonAtPos G (n + 1) j X ≫
              deltaAtPos G (n + 1) i X := by
                rw [h_ε, h_δ]

/-- The mixed insertion identity with counit after comultiplication.

For left-end positions `i<j`, comultiplication at `i.castSucc` followed by counit at `j.succ`
equals counit at `j` followed by comultiplication at `i`. -/
theorem deltaAtPos_epsilonAtPos_castSucc_succ_of_lt (n : ℕ) (i : Fin n)
    (j : Fin (n + 1)) (h : i.val < j.val) (X : C) :
    deltaAtPos G (n + 1) i.castSucc X ≫ epsilonAtPos G (n + 1) j.succ X =
      epsilonAtPos G n j X ≫ deltaAtPos G n i X := by
  induction n generalizing X with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    have hj_pos : 0 < j.val := by omega
    have hj_sub : j.val - 1 < n + 1 := by omega
    let j0 : Fin (n + 1) := ⟨j.val - 1, hj_sub⟩
    have hj_eq : j = j0.succ := by
      apply Fin.ext
      simp [j0, Fin.succ]
      omega
    by_cases hi0 : i.val = 0
    · have hi_eq : i = ⟨0, Nat.succ_pos _⟩ := by apply Fin.ext; omega
      have hi_cast_zero : (⟨0, Nat.succ_pos _⟩ : Fin (n + 1)).castSucc =
          (⟨0, Nat.succ_pos _⟩ : Fin (n + 2)) := by
        apply Fin.ext; simp
      have hi_cast_eq : i.castSucc = (⟨0, Nat.succ_pos _⟩ : Fin (n + 2)) := by
        rw [hi_eq]
        exact hi_cast_zero
      have h_δ_zero' : deltaAtPos G (n + 1)
          (⟨0, Nat.succ_pos _⟩ : Fin (n + 1)) X =
          (comonadPow G n).map (G.δ.app X) := rfl
      have h_eps_j0 : epsilonAtPos G (n + 1) j0.succ X =
          epsilonAtPos G n j0 (G.toFunctor.obj X) := rfl
      calc deltaAtPos G (n + 2) i.castSucc X ≫ epsilonAtPos G (n + 2) j.succ X
          = deltaAtPos G (n + 2) (⟨0, Nat.succ_pos _⟩ : Fin (n + 2)) X ≫
            epsilonAtPos G (n + 2) (j0.succ.succ) X := by
            rw [hi_cast_eq, hj_eq]
      _ = (comonadPow G (n + 1)).map (G.δ.app X) ≫
            epsilonAtPos G n j0 (G.toFunctor.obj (G.toFunctor.obj X)) := rfl
      _ = epsilonAtPos G n j0 (G.toFunctor.obj X) ≫
            (comonadPow G n).map (G.δ.app X) := by
            have hnat := epsilonAtPos_naturality G n j0 (f := G.δ.app X)
            exact hnat
      _ = epsilonAtPos G (n + 1) j0.succ X ≫
            deltaAtPos G (n + 1) (⟨0, Nat.succ_pos _⟩ : Fin (n + 1)) X := by
            rw [h_eps_j0, h_δ_zero']
      _ = epsilonAtPos G (n + 1) j X ≫ deltaAtPos G (n + 1) i X := by
            rw [hj_eq, hi_eq]
    · have hi_pos : 0 < i.val := by omega
      have hi_sub : i.val - 1 < n := by omega
      let i0 : Fin n := ⟨i.val - 1, hi_sub⟩
      have hi_eq : i = i0.succ := by
        apply Fin.ext
        simp [i0, Fin.succ]
        omega
      have hi_lt_j0 : i0.val < j0.val := by
        have e1 : i0.val = i.val - 1 := rfl
        have e2 : j0.val = j.val - 1 := rfl
        omega
      have hi_cast_eq : i.castSucc = (i0.castSucc).succ := by
        apply Fin.ext
        simp [i0, Fin.castSucc, Fin.succ]
        omega
      have hj_succ_eq : j.succ = (j0.succ).succ := by
        apply Fin.ext
        simp [j0, Fin.succ]
        omega
      have h_δ_cast_succ : deltaAtPos G (n + 2) i.castSucc X =
          deltaAtPos G (n + 1) i0.castSucc (G.toFunctor.obj X) := by
        rw [hi_cast_eq]
        rfl
      have h_ε_succ : epsilonAtPos G (n + 2) j.succ X =
          epsilonAtPos G (n + 1) j (G.toFunctor.obj X) := rfl
      have h_δ : deltaAtPos G (n + 1) i X =
          deltaAtPos G n i0 (G.toFunctor.obj X) := by
        rw [hi_eq]
        rfl
      have h_ε : epsilonAtPos G (n + 1) j X =
          epsilonAtPos G n j0 (G.toFunctor.obj X) := by
        rw [hj_eq]
        rfl
      calc deltaAtPos G (n + 2) i.castSucc X ≫ epsilonAtPos G (n + 2) j.succ X
          = deltaAtPos G (n + 1) i0.castSucc (G.toFunctor.obj X) ≫
            epsilonAtPos G (n + 1) j (G.toFunctor.obj X) := by
            rw [h_δ_cast_succ, h_ε_succ]
      _ = deltaAtPos G (n + 1) i0.castSucc (G.toFunctor.obj X) ≫
            epsilonAtPos G (n + 1) j0.succ (G.toFunctor.obj X) := by
            rw [hj_eq]
      _ = epsilonAtPos G n j0 (G.toFunctor.obj X) ≫
            deltaAtPos G n i0 (G.toFunctor.obj X) :=
            ih i0 j0 hi_lt_j0 (G.toFunctor.obj X)
      _ = epsilonAtPos G (n + 1) j X ≫
            deltaAtPos G (n + 1) i X := by
            rw [h_ε, h_δ]

end DeltaEpsilonDistant

section CofaceCodegSelf

variable {G : Comonad C} {R : RightComodule G D} {L : LeftComodule A G}

/-- The componentwise matching coface–codegeneracy identity.

For `i : Fin (n+1)`, coface `i` followed by codegeneracy `i` is the identity at every carrier
object. -/
theorem cobarCofaceApp_codegeneracy_self (n : ℕ) (i : Fin (n + 1)) (a : A) :
    cobarCofaceApp (G := G) (R := R) (L := L) n i.castSucc a ≫
      (cobarCodegeneracy (G := G) (R := R) (L := L) n i).app a = 𝟙 _ := by
  let X := L.functor.obj a
  by_cases h0 : i.val = 0
  · have hi_cast_val : (Fin.castSucc i : Fin (n + 2)).val = 0 := by
      simp [Fin.castSucc, h0]
    have h_face : cobarCofaceApp (G := G) (R := R) (L := L) n
        (Fin.castSucc i) a = rightCoactionPow G R n X :=
      cobarCofaceApp_of_val_zero (G := G) (R := R) (L := L) hi_cast_val
    have h_rev : i.rev = ⟨n, by omega⟩ := by apply Fin.ext; simp [Fin.rev, h0]
    have h_deg : (cobarCodegeneracy (G := G) (R := R) (L := L) n i).app a =
        R.functor.map (epsilonAtPos G n ⟨n, by omega⟩ X) := by
      simp only [cobarCodegeneracy_app, cobarEpsilonAtPos_rev]
      rw [h_rev]
    rw [h_face, h_deg]
    exact rightCoactionPow_counit_last (G := G) (R := R) n X
  · have hi_pos : 0 < i.val := by omega
    have hn : 0 < n := by omega
    let k : Fin n := ⟨i.val - 1, by omega⟩
    have hi_eq : i.val = k.val + 1 := by have hk : k.val = i.val - 1 := rfl; omega
    have hi_cast_eq : (Fin.castSucc i : Fin (n + 2)).val = k.val + 1 := by
      simp [Fin.castSucc, hi_eq]
    have h_face : cobarCofaceApp (G := G) (R := R) (L := L) n
        (Fin.castSucc i) a = R.functor.map (cobarDeltaAtPos G n k X) :=
      cobarCofaceApp_of_middle (G := G) (R := R) (L := L) (k := k) hi_cast_eq
    have h_rev_eq : i.rev = (k.rev).castSucc := by
      apply Fin.ext; simp [Fin.rev, k]; omega
    have h_deg : (cobarCodegeneracy (G := G) (R := R) (L := L) n i).app a =
        R.functor.map (epsilonAtPos G n (k.rev).castSucc X) := by
      simp only [cobarCodegeneracy_app, cobarEpsilonAtPos_rev]
      rw [h_rev_eq]
    have h_δ : cobarDeltaAtPos G n k X = deltaAtPos G n k.rev X := rfl
    rw [h_face, h_deg, h_δ]
    calc R.functor.map (deltaAtPos G n k.rev X) ≫
            R.functor.map (epsilonAtPos G n (k.rev).castSucc X)
        = R.functor.map (deltaAtPos G n k.rev X ≫
            epsilonAtPos G n (k.rev).castSucc X) := by
          rw [← R.functor.map_comp]
      _ = R.functor.map (𝟙 _) := by
          rw [deltaAtPos_epsilonAtPos_castSucc]
      _ = 𝟙 _ := by
          rw [R.functor.map_id]

/-- The matching coface–codegeneracy identity of cobar functors.

The composite `δ_n^i ≫ σ_n^i` is the identity on degree `n`. -/
theorem cobarCoface_codegeneracy_self (n : ℕ) (i : Fin (n + 1)) :
    cobarCoface (G := G) (R := R) (L := L) n i.castSucc ≫
      cobarCodegeneracy (G := G) (R := R) (L := L) n i =
    𝟙 (cobarObj G R L n) := by
  ext a; exact cobarCofaceApp_codegeneracy_self (G := G) (R := R) (L := L) n i a

end CofaceCodegSelf

section CofaceCodegSucc

variable {G : Comonad C} {R : RightComodule G D} {L : LeftComodule A G}

/-- The componentwise successor coface–codegeneracy identity.

For `i : Fin (n+1)`, coface `i+1` followed by codegeneracy `i` is the identity at every
carrier object. -/
theorem cobarCofaceApp_codegeneracy_succ (n : ℕ) (i : Fin (n + 1)) (a : A) :
    cobarCofaceApp (G := G) (R := R) (L := L) n i.succ a ≫
      (cobarCodegeneracy (G := G) (R := R) (L := L) n i).app a = 𝟙 _ := by
  let X := L.functor.obj a
  by_cases h_last : i.val = n
  · have hi_succ_val : (Fin.succ i : Fin (n + 2)).val = n + 1 := by
      simp [Fin.succ, h_last]
    have h_face : cobarCofaceApp (G := G) (R := R) (L := L) n
        (Fin.succ i) a =
        R.functor.map ((comonadPow G n).map (L.coaction.app a)) :=
      cobarCofaceApp_of_val_last (G := G) (R := R) (L := L) hi_succ_val
    have h_rev : i.rev = ⟨0, by omega⟩ := by apply Fin.ext; simp [Fin.rev, h_last]
    have h_deg : (cobarCodegeneracy (G := G) (R := R) (L := L) n i).app a =
        R.functor.map (epsilonAtPos G n ⟨0, by omega⟩ X) := by
      simp only [cobarCodegeneracy_app, cobarEpsilonAtPos_rev]
      rw [h_rev]
    rw [h_face, h_deg]
    exact leftCoaction_epsilon_zero (G := G) (R := R) (L := L) n a
  · have hi_lt : i.val < n := by omega
    let k : Fin n := ⟨i.val, by omega⟩
    have hi_succ_eq : (Fin.succ i : Fin (n + 2)).val = k.val + 1 := by
      simp [Fin.succ, k]
    have h_face : cobarCofaceApp (G := G) (R := R) (L := L) n
        (Fin.succ i) a = R.functor.map (cobarDeltaAtPos G n k X) :=
      cobarCofaceApp_of_middle (G := G) (R := R) (L := L) (k := k) hi_succ_eq
    have h_rev_eq : i.rev = (k.rev).succ := by
      apply Fin.ext; simp [Fin.rev, k]; omega
    have h_deg : (cobarCodegeneracy (G := G) (R := R) (L := L) n i).app a =
        R.functor.map (epsilonAtPos G n (k.rev).succ X) := by
      simp only [cobarCodegeneracy_app, cobarEpsilonAtPos_rev]
      rw [h_rev_eq]
    have h_δ : cobarDeltaAtPos G n k X = deltaAtPos G n k.rev X := rfl
    rw [h_face, h_deg, h_δ]
    calc R.functor.map (deltaAtPos G n k.rev X) ≫
            R.functor.map (epsilonAtPos G n (k.rev).succ X)
        = R.functor.map (deltaAtPos G n k.rev X ≫
            epsilonAtPos G n (k.rev).succ X) := by
          rw [← R.functor.map_comp]
      _ = R.functor.map (𝟙 _) := by
          rw [deltaAtPos_epsilonAtPos_succ]
      _ = 𝟙 _ := by
          rw [R.functor.map_id]

/-- The successor coface–codegeneracy identity of cobar functors.

The composite `δ_n^(i+1) ≫ σ_n^i` is the identity on degree `n`. -/
theorem cobarCoface_codegeneracy_succ (n : ℕ) (i : Fin (n + 1)) :
    cobarCoface (G := G) (R := R) (L := L) n i.succ ≫
      cobarCodegeneracy (G := G) (R := R) (L := L) n i =
    𝟙 (cobarObj G R L n) := by
  ext a; exact cobarCofaceApp_codegeneracy_succ (G := G) (R := R) (L := L) n i a

end CofaceCodegSucc

section CofaceCodegOfLe

variable {G : Comonad C} {R : RightComodule G D} {L : LeftComodule A G}

/-- The componentwise mixed cobar identity for a preceding coface.

For `i ≤ j`, the components satisfy `δ_(n+1)^i ≫ σ_(n+1)^(j+1) = σ_n^j ≫ δ_n^i`. -/
theorem cobarCofaceApp_codegeneracy_of_le {n : ℕ} {i : Fin (n + 2)}
    {j : Fin (n + 1)} (h : i ≤ j.castSucc) (a : A) :
    cobarCofaceApp (G := G) (R := R) (L := L) (n + 1) i.castSucc a ≫
      (cobarCodegeneracy (G := G) (R := R) (L := L) (n + 1) j.succ).app a =
    (cobarCodegeneracy (G := G) (R := R) (L := L) n j).app a ≫
      cobarCofaceApp (G := G) (R := R) (L := L) n i a := by
  let X := L.functor.obj a
  have h_val : i.val ≤ j.val := by
    have := Fin.le_def.mp h
    simpa using this
  by_cases hi0 : i.val = 0
  · have h_face_n : cobarCofaceApp (G := G) (R := R) (L := L) n i a =
        rightCoactionPow G R n X :=
      cobarCofaceApp_of_val_zero (G := G) (R := R) (L := L) hi0
    have h_cast_zero : (Fin.castSucc i : Fin (n + 3)).val = 0 := by simp [hi0]
    have h_face_Sn : cobarCofaceApp (G := G) (R := R) (L := L) (n + 1)
        i.castSucc a = rightCoactionPow G R (n + 1) X :=
      cobarCofaceApp_of_val_zero (G := G) (R := R) (L := L) h_cast_zero
    have h_rev_succ : (j.succ : Fin (n + 2)).rev = j.rev.castSucc :=
      Fin.rev_succ j
    have h_ε_Sn : cobarEpsilonAtPos G (n + 1) j.succ X =
        epsilonAtPos G (n + 1) j.rev.castSucc X := by
      simp only [cobarEpsilonAtPos_rev, h_rev_succ]
    have h_ε_n : cobarEpsilonAtPos G n j X = epsilonAtPos G n j.rev X := rfl
    calc cobarCofaceApp (G := G) (R := R) (L := L) (n + 1) i.castSucc a ≫
            (cobarCodegeneracy (G := G) (R := R) (L := L) (n + 1) j.succ).app a
        = rightCoactionPow G R (n + 1) X ≫
            R.functor.map (cobarEpsilonAtPos G (n + 1) j.succ X) := by
          rw [h_face_Sn]
          rfl
      _ = rightCoactionPow G R (n + 1) X ≫
            R.functor.map (epsilonAtPos G (n + 1) j.rev.castSucc X) := by
          rw [h_ε_Sn]
      _ = R.functor.map (epsilonAtPos G n j.rev X) ≫
            rightCoactionPow G R n X := by
          exact rightCoactionPow_epsilon_castSucc (G := G) (R := R) n j.rev X
      _ = R.functor.map (cobarEpsilonAtPos G n j X) ≫
            rightCoactionPow G R n X := by
          rw [h_ε_n]
      _ = (cobarCodegeneracy (G := G) (R := R) (L := L) n j).app a ≫
            cobarCofaceApp (G := G) (R := R) (L := L) n i a := by
          rw [h_face_n]
          rfl
  · have hi_not_last : i.val ≠ n + 1 := by
      intro h_last
      have : j.val ≤ n := by have := j.isLt; omega
      omega
    have hi_pos : 0 < i.val := by omega
    have hi_le_n : i.val ≤ n := by omega
    have hk_n : i.val - 1 < n := by omega
    let i0 : Fin n := ⟨i.val - 1, hk_n⟩
    have hi_eq : i.val = i0.val + 1 := by have : i0.val = i.val - 1 := rfl; omega
    have h_face_n : cobarCofaceApp (G := G) (R := R) (L := L) n i a =
        R.functor.map (cobarDeltaAtPos G n i0 X) :=
      cobarCofaceApp_of_middle (G := G) (R := R) (L := L) (k := i0) hi_eq
    have hk_Sn : i.val - 1 < n + 1 := by omega
    let i0c : Fin (n + 1) := ⟨i.val - 1, hk_Sn⟩
    have hi0c_eq : i0c = i0.castSucc := by apply Fin.ext; rfl
    have hi0c_val : i0c.val = i0.val := rfl
    have h_cast_eq : (Fin.castSucc i : Fin (n + 3)).val = i0c.val + 1 := by
      have h1 : (Fin.castSucc i).val = i.val := rfl
      have h2 : i.val = i0.val + 1 := hi_eq
      have h3 : i0.val = i0c.val := by rw [hi0c_val]
      omega
    have h_face_Sn : cobarCofaceApp (G := G) (R := R) (L := L) (n + 1)
        i.castSucc a = R.functor.map (cobarDeltaAtPos G (n + 1) i0c X) :=
      cobarCofaceApp_of_middle (G := G) (R := R) (L := L) (k := i0c) h_cast_eq
    have h_rev_succ : (j.succ : Fin (n + 2)).rev = j.rev.castSucc :=
      Fin.rev_succ j
    have h_ε_Sn : cobarEpsilonAtPos G (n + 1) j.succ X =
        epsilonAtPos G (n + 1) j.rev.castSucc X := by
      simp only [cobarEpsilonAtPos_rev, h_rev_succ]
    have h_ε_n : cobarEpsilonAtPos G n j X = epsilonAtPos G n j.rev X := rfl
    have h_δ_n : cobarDeltaAtPos G n i0 X = deltaAtPos G n i0.rev X := rfl
    have h_rev_cast : i0c.rev = i0.rev.succ := by
      rw [hi0c_eq]; exact Fin.rev_castSucc i0
    have h_δ_Sn : cobarDeltaAtPos G (n + 1) i0c X =
        deltaAtPos G (n + 1) i0.rev.succ X := by
      calc cobarDeltaAtPos G (n + 1) i0c X = deltaAtPos G (n + 1) i0c.rev X :=
            rfl
        _ = deltaAtPos G (n + 1) i0.rev.succ X := by rw [h_rev_cast]
    have h_le_rev : j.rev.val ≤ i0.rev.val := by
      have hj_rev : j.rev.val = n - j.val := by simp [Fin.rev]
      have hi_rev : i0.rev.val = (n - 1) - i0.val := by simp [Fin.rev, i0]; omega
      omega
    have h_inter := deltaAtPos_epsilonAtPos_succ_castSucc_of_le
      (G := G) n i0.rev j.rev h_le_rev X
    calc cobarCofaceApp (G := G) (R := R) (L := L) (n + 1) i.castSucc a ≫
            (cobarCodegeneracy (G := G) (R := R) (L := L) (n + 1) j.succ).app a
        = R.functor.map (cobarDeltaAtPos G (n + 1) i0c X) ≫
            R.functor.map (cobarEpsilonAtPos G (n + 1) j.succ X) := by
          rw [h_face_Sn]
          rfl
      _ = R.functor.map (deltaAtPos G (n + 1) i0.rev.succ X) ≫
            R.functor.map (epsilonAtPos G (n + 1) j.rev.castSucc X) := by
          rw [h_δ_Sn, h_ε_Sn]
      _ = R.functor.map (deltaAtPos G (n + 1) i0.rev.succ X ≫
            epsilonAtPos G (n + 1) j.rev.castSucc X) := by
          rw [← R.functor.map_comp]
      _ = R.functor.map (epsilonAtPos G n j.rev X ≫
            deltaAtPos G n i0.rev X) := by
          rw [h_inter]
      _ = R.functor.map (epsilonAtPos G n j.rev X) ≫
            R.functor.map (deltaAtPos G n i0.rev X) := by
          rw [R.functor.map_comp]
      _ = R.functor.map (cobarEpsilonAtPos G n j X) ≫
            R.functor.map (cobarDeltaAtPos G n i0 X) := by
          rw [h_ε_n, h_δ_n]
      _ = (cobarCodegeneracy (G := G) (R := R) (L := L) n j).app a ≫
            cobarCofaceApp (G := G) (R := R) (L := L) n i a := by
          rw [h_face_n]
          rfl

/-- The mixed cobar identity for a preceding coface.

For `i ≤ j`, the natural transformations satisfy `δ_(n+1)^i ≫ σ_(n+1)^(j+1) = σ_n^j ≫ δ_n^i`. -/
theorem cobarCoface_codegeneracy_of_le {n : ℕ} {i : Fin (n + 2)}
    {j : Fin (n + 1)} (h : i ≤ j.castSucc) :
    cobarCoface (G := G) (R := R) (L := L) (n + 1) i.castSucc ≫
      cobarCodegeneracy (G := G) (R := R) (L := L) (n + 1) j.succ =
    cobarCodegeneracy (G := G) (R := R) (L := L) n j ≫
      cobarCoface (G := G) (R := R) (L := L) n i := by
  ext a; exact cobarCofaceApp_codegeneracy_of_le (G := G) (R := R) (L := L) h a

end CofaceCodegOfLe

section CofaceCodegOfGt

variable {G : Comonad C} {R : RightComodule G D} {L : LeftComodule A G}

/-- The componentwise mixed cobar identity for a following coface.

For `j<i`, the components satisfy `δ_(n+1)^(i+1) ≫ σ_(n+1)^j = σ_n^j ≫ δ_n^i`. -/
theorem cobarCofaceApp_codegeneracy_of_gt {n : ℕ} {i : Fin (n + 2)}
    {j : Fin (n + 1)} (h : j.castSucc < i) (a : A) :
    cobarCofaceApp (G := G) (R := R) (L := L) (n + 1) i.succ a ≫
      (cobarCodegeneracy (G := G) (R := R) (L := L) (n + 1) j.castSucc).app a =
    (cobarCodegeneracy (G := G) (R := R) (L := L) n j).app a ≫
      cobarCofaceApp (G := G) (R := R) (L := L) n i a := by
  let X := L.functor.obj a
  have h_val : j.val < i.val := by have := Fin.lt_def.mp h; simpa using this
  have hi_pos : 0 < i.val := by omega
  by_cases hi_last : i.val = n + 1
  · have h_face_n : cobarCofaceApp (G := G) (R := R) (L := L) n i a =
        R.functor.map ((comonadPow G n).map (L.coaction.app a)) :=
      cobarCofaceApp_of_val_last (G := G) (R := R) (L := L) hi_last
    have h_succ_last : (Fin.succ i : Fin (n + 3)).val = n + 2 := by
      simp [Fin.succ, hi_last]
    have h_face_Sn : cobarCofaceApp (G := G) (R := R) (L := L) (n + 1)
        i.succ a =
        R.functor.map ((comonadPow G (n + 1)).map (L.coaction.app a)) :=
      cobarCofaceApp_of_val_last (G := G) (R := R) (L := L) h_succ_last
    have h_rev_cast : (Fin.castSucc j : Fin (n + 2)).rev = j.rev.succ :=
      Fin.rev_castSucc j
    have h_ε_Sn : cobarEpsilonAtPos G (n + 1) j.castSucc X =
        epsilonAtPos G (n + 1) j.rev.succ X := by
      simp only [cobarEpsilonAtPos_rev, h_rev_cast]
    have h_ε_n : cobarEpsilonAtPos G n j X = epsilonAtPos G n j.rev X := rfl
    calc cobarCofaceApp (G := G) (R := R) (L := L) (n + 1) i.succ a ≫
            (cobarCodegeneracy (G := G) (R := R) (L := L) (n + 1)
              j.castSucc).app a
        = R.functor.map ((comonadPow G (n + 1)).map (L.coaction.app a)) ≫
            R.functor.map (cobarEpsilonAtPos G (n + 1) j.castSucc X) := by
          rw [h_face_Sn]
          rfl
      _ = R.functor.map ((comonadPow G (n + 1)).map (L.coaction.app a)) ≫
            R.functor.map (epsilonAtPos G (n + 1) j.rev.succ X) := by
          rw [h_ε_Sn]
      _ = R.functor.map (epsilonAtPos G n j.rev X) ≫
            R.functor.map ((comonadPow G n).map (L.coaction.app a)) := by
          have hnat := leftCoaction_epsilon_naturality (G := G) (L := L)
            n j.rev a
          have hεs : epsilonAtPos G (n + 1) j.rev.succ X =
              epsilonAtPos G n j.rev (G.toFunctor.obj X) := rfl
          have hY : (comonadPow G (n + 1)).map (L.coaction.app a) =
              (comonadPow G n).map
                (G.toFunctor.map (L.coaction.app a)) := rfl
          rw [hY] at hnat
          rw [hεs, hY, ← R.functor.map_comp, ← R.functor.map_comp, hnat]
      _ = R.functor.map (cobarEpsilonAtPos G n j X) ≫
            R.functor.map ((comonadPow G n).map (L.coaction.app a)) := by
          rw [h_ε_n]
      _ = (cobarCodegeneracy (G := G) (R := R) (L := L) n j).app a ≫
            cobarCofaceApp (G := G) (R := R) (L := L) n i a := by
          rw [h_face_n]
          rfl
  · have hi_not_last : i.val ≠ n + 1 := hi_last
    have hi_le_n : i.val ≤ n := by omega
    have hk_n : i.val - 1 < n := by omega
    let i0 : Fin n := ⟨i.val - 1, hk_n⟩
    have hi_eq : i.val = i0.val + 1 := by
      have : i0.val = i.val - 1 := rfl
      omega
    have h_face_n : cobarCofaceApp (G := G) (R := R) (L := L) n i a =
        R.functor.map (cobarDeltaAtPos G n i0 X) :=
      cobarCofaceApp_of_middle (G := G) (R := R) (L := L) (k := i0) hi_eq
    have hk_Sn1 : i.val < n + 1 := by omega
    let i0s : Fin (n + 1) := ⟨i.val, hk_Sn1⟩
    have hi0s_eq : i0s = i0.succ := by
      apply Fin.ext; have : i0s.val = i.val := rfl
      have : (i0.succ).val = i0.val + 1 := rfl; omega
    have h_succ_eq : (Fin.succ i : Fin (n + 3)).val = i0s.val + 1 := by
      have : (Fin.succ i).val = i.val + 1 := rfl
      have : i0s.val = i.val := rfl; omega
    have h_face_Sn : cobarCofaceApp (G := G) (R := R) (L := L) (n + 1)
        i.succ a = R.functor.map (cobarDeltaAtPos G (n + 1) i0s X) :=
      cobarCofaceApp_of_middle (G := G) (R := R) (L := L) (k := i0s) h_succ_eq
    have h_rev_cast : (Fin.castSucc j : Fin (n + 2)).rev = j.rev.succ :=
      Fin.rev_castSucc j
    have h_ε_Sn : cobarEpsilonAtPos G (n + 1) j.castSucc X =
        epsilonAtPos G (n + 1) j.rev.succ X := by
      simp only [cobarEpsilonAtPos_rev, h_rev_cast]
    have h_ε_n : cobarEpsilonAtPos G n j X = epsilonAtPos G n j.rev X := rfl
    have h_δ_n : cobarDeltaAtPos G n i0 X = deltaAtPos G n i0.rev X := rfl
    have h_rev_succ : i0s.rev = i0.rev.castSucc := by
      rw [hi0s_eq]
      exact Fin.rev_succ i0
    have h_δ_Sn : cobarDeltaAtPos G (n + 1) i0s X =
        deltaAtPos G (n + 1) i0.rev.castSucc X := by
      calc cobarDeltaAtPos G (n + 1) i0s X = deltaAtPos G (n + 1) i0s.rev X :=
            rfl
        _ = deltaAtPos G (n + 1) i0.rev.castSucc X := by rw [h_rev_succ]
    have h_lt_rev : i0.rev.val < j.rev.val := by
      have hj_rev : j.rev.val = (n + 1) - (j.val + 1) := rfl
      have hi_rev : i0.rev.val = (n - 1) - i0.val := by
        simp [Fin.rev, i0]
        omega
      omega
    have h_inter := deltaAtPos_epsilonAtPos_castSucc_succ_of_lt
      (G := G) n i0.rev j.rev h_lt_rev X
    calc cobarCofaceApp (G := G) (R := R) (L := L) (n + 1) i.succ a ≫
            (cobarCodegeneracy (G := G) (R := R) (L := L) (n + 1)
              j.castSucc).app a
        = R.functor.map (cobarDeltaAtPos G (n + 1) i0s X) ≫
            R.functor.map (cobarEpsilonAtPos G (n + 1) j.castSucc X) := by
          rw [h_face_Sn]
          rfl
      _ = R.functor.map (deltaAtPos G (n + 1) i0.rev.castSucc X) ≫
            R.functor.map (epsilonAtPos G (n + 1) j.rev.succ X) := by
          rw [h_δ_Sn, h_ε_Sn]
      _ = R.functor.map (deltaAtPos G (n + 1) i0.rev.castSucc X ≫
            epsilonAtPos G (n + 1) j.rev.succ X) := by
          rw [← R.functor.map_comp]
      _ = R.functor.map (epsilonAtPos G n j.rev X ≫
            deltaAtPos G n i0.rev X) := by
          rw [h_inter]
      _ = R.functor.map (epsilonAtPos G n j.rev X) ≫
            R.functor.map (deltaAtPos G n i0.rev X) := by
          rw [R.functor.map_comp]
      _ = R.functor.map (cobarEpsilonAtPos G n j X) ≫
            R.functor.map (cobarDeltaAtPos G n i0 X) := by
          rw [h_ε_n, h_δ_n]
      _ = (cobarCodegeneracy (G := G) (R := R) (L := L) n j).app a ≫
            cobarCofaceApp (G := G) (R := R) (L := L) n i a := by
          rw [h_face_n]
          rfl

/-- The mixed cobar identity for a following coface.

For `j<i`, the natural transformations satisfy `δ_(n+1)^(i+1) ≫ σ_(n+1)^j = σ_n^j ≫ δ_n^i`. -/
theorem cobarCoface_codegeneracy_of_gt {n : ℕ} {i : Fin (n + 2)}
    {j : Fin (n + 1)} (h : j.castSucc < i) :
    cobarCoface (G := G) (R := R) (L := L) (n + 1) i.succ ≫
      cobarCodegeneracy (G := G) (R := R) (L := L) (n + 1) j.castSucc =
    cobarCodegeneracy (G := G) (R := R) (L := L) n j ≫
      cobarCoface (G := G) (R := R) (L := L) n i := by
  ext a; exact cobarCofaceApp_codegeneracy_of_gt (G := G) (R := R) (L := L) h a

end CofaceCodegOfGt

section EndpointTrichotomy

variable {G : Comonad C} {R : RightComodule G D} {L : LeftComodule A G}

/-- The endpoint and interior cases of a cobar coface index.

Every `i : Fin (n+2)` has value zero, value `n+1`, or value `k+1` for an interior index `k :
Fin n`. -/
theorem cobarCofaceIndex_trichotomy (n : ℕ) (i : Fin (n + 2)) :
    i.val = 0 ∨ i.val = n + 1 ∨ ∃ k : Fin n, i.val = k.val + 1 := by
  by_cases h0 : i.val = 0; · exact Or.inl h0
  · by_cases hlast : i.val = n + 1; · exact Or.inr (Or.inl hlast)
    · have hk : i.val - 1 < n := by omega
      refine Or.inr (Or.inr ⟨⟨i.val - 1, hk⟩, ?_⟩)
      have hval : (⟨i.val - 1, hk⟩ : Fin n).val = i.val - 1 := rfl
      omega

/-- The reversed insertion position of the first interior cobar coface.

The right-end insertion at zero is the left-end comultiplication insertion at the final
position. -/
@[simp] theorem cobarDeltaAtPos_rev_zero (n : ℕ) (X : C) :
    cobarDeltaAtPos G (n + 1) ⟨0, by omega⟩ X =
      deltaAtPos G (n + 1) ⟨n, by omega⟩ X := by
  simp only [cobarDeltaAtPos]; congr 1

/-- The reversed insertion position of the last interior cobar coface.

The right-end insertion at the final position is the left-end comultiplication insertion at
zero. -/
@[simp] theorem cobarDeltaAtPos_rev_last (n : ℕ) (X : C) :
    cobarDeltaAtPos G (n + 1) ⟨n, by omega⟩ X =
      deltaAtPos G (n + 1) ⟨0, by omega⟩ X := by
  simp only [cobarDeltaAtPos]; congr 1; apply Fin.ext; simp [Fin.rev]

end EndpointTrichotomy

section CobarData

variable {G : Comonad C} {R : RightComodule G D} {L : LeftComodule A G}

/-- The opposite simplicial data of a two-sided cobar construction.

Take the opposite degree functors `R(G^n(L(-)))`, with the opposites of their cofaces and
codegeneracies as simplicial operators. -/
noncomputable def cobarDataOp (G : Comonad C) (R : RightComodule G D)
    (L : LeftComodule A G) : SimplicialObject.Data ((A ⥤ D)ᵒᵖ) where
  obj n := Opposite.op (cobarObj G R L n)
  δ i := (cobarCoface (G := G) (R := R) (L := L) _ i).op
  σ i := (cobarCodegeneracy (G := G) (R := R) (L := L) _ i).op
  δ_comp_δ := fun {n} {i j} h => by
    apply Quiver.Hom.unop_inj
    simp only [unop_comp, Quiver.Hom.unop_op]
    exact cobarCoface_coface_coface (G := G) (R := R) (L := L) n i j h
  δ_comp_σ_of_le := fun {n} {i j} h => by
    apply Quiver.Hom.unop_inj
    simp only [unop_comp, Quiver.Hom.unop_op]
    exact cobarCoface_codegeneracy_of_le (G := G) (R := R) (L := L) h
  δ_comp_σ_self := fun {n} {i} => by
    apply Quiver.Hom.unop_inj
    simp only [unop_comp, Quiver.Hom.unop_op, unop_id]
    exact cobarCoface_codegeneracy_self (G := G) (R := R) (L := L) n i
  δ_comp_σ_succ := fun {n} {i} => by
    apply Quiver.Hom.unop_inj
    simp only [unop_comp, Quiver.Hom.unop_op, unop_id]
    exact cobarCoface_codegeneracy_succ (G := G) (R := R) (L := L) n i
  δ_comp_σ_of_gt := fun {n} {i j} h => by
    apply Quiver.Hom.unop_inj
    simp only [unop_comp, Quiver.Hom.unop_op]
    exact cobarCoface_codegeneracy_of_gt (G := G) (R := R) (L := L) h
  σ_comp_σ := fun {n} {i j} h => by
    apply Quiver.Hom.unop_inj
    simp only [unop_comp, Quiver.Hom.unop_op]
    exact cobarCodegeneracy_deg_deg (G := G) (R := R) (L := L) n i j h

/-- The degree-object family of opposite cobar data.

The object family sends `n` to the opposite of the degree-`n` cobar functor. -/
@[simp] theorem cobarDataOp_obj (G : Comonad C) (R : RightComodule G D)
    (L : LeftComodule A G) :
    (cobarDataOp G R L).obj = fun n => Opposite.op (cobarObj G R L n) :=
  rfl

/-- The object in one degree of opposite cobar data.

In degree `n`, the object is `op(cobarObj G R L n)`. -/
@[simp] theorem cobarDataOp_obj_n (G : Comonad C) (R : RightComodule G D)
    (L : LeftComodule A G) (n : ℕ) :
    (cobarDataOp G R L).obj n = Opposite.op (cobarObj G R L n) :=
  rfl

/-- The face maps of opposite cobar data.

The simplicial face at `i` is the opposite of cobar coface `i`. -/
@[simp] theorem cobarDataOp_δ (G : Comonad C) (R : RightComodule G D)
    (L : LeftComodule A G) {n : ℕ} (i : Fin (n + 2)) :
    (cobarDataOp G R L).δ i =
      (cobarCoface (G := G) (R := R) (L := L) n i).op :=
  rfl

/-- The degeneracy maps of opposite cobar data.

The simplicial degeneracy at `i` is the opposite of cobar codegeneracy `i`. -/
@[simp] theorem cobarDataOp_σ (G : Comonad C) (R : RightComodule G D)
    (L : LeftComodule A G) {n : ℕ} (i : Fin (n + 1)) :
    (cobarDataOp G R L).σ i =
      (cobarCodegeneracy (G := G) (R := R) (L := L) n i).op :=
  rfl

/-- The opposite cobar functor on the generated simplex category.

The cosimplicial identities extend the opposite cobar data to a functor from the opposite
generator-and-relation simplex category. -/
noncomputable def cobarGenRelOp (G : Comonad C) (R : RightComodule G D)
    (L : LeftComodule A G) : SimplexCategoryGenRelᵒᵖ ⥤ (A ⥤ D)ᵒᵖ :=
  (cobarDataOp G R L).toGenRelFunctor

/-- The finite-ordinal value of the generated opposite cobar functor.

At the opposite ordinal of degree `n`, the value is the opposite degree-`n` cobar functor. -/
@[simp] theorem cobarGenRelOp_obj_op_mk (G : Comonad C)
    (R : RightComodule G D) (L : LeftComodule A G) (n : ℕ) :
    (cobarGenRelOp G R L).obj (Opposite.op (SimplexCategoryGenRel.mk n)) =
      Opposite.op (cobarObj G R L n) :=
  rfl

/-- The generated opposite cobar map of a coface generator.

The opposite coface generator maps to the opposite of the corresponding cobar coface. -/
theorem cobarGenRelOp_map_δ_op (G : Comonad C) (R : RightComodule G D)
    (L : LeftComodule A G) {n : ℕ} (i : Fin (n + 2)) :
    (cobarGenRelOp G R L).map (SimplexCategoryGenRel.δ (n := n) i).op =
      (cobarCoface (G := G) (R := R) (L := L) n i).op :=
  SimplicialObject.Data.toGenRelFunctor_map_δ_op
    (cobarDataOp G R L) (n := n) i

/-- The generated opposite cobar map of a codegeneracy generator.

The opposite codegeneracy generator maps to the opposite of the corresponding cobar
codegeneracy. -/
theorem cobarGenRelOp_map_σ_op (G : Comonad C) (R : RightComodule G D)
    (L : LeftComodule A G) {n : ℕ} (i : Fin (n + 1)) :
    (cobarGenRelOp G R L).map (SimplexCategoryGenRel.σ (n := n) i).op =
      (cobarCodegeneracy (G := G) (R := R) (L := L) n i).op :=
  SimplicialObject.Data.toGenRelFunctor_map_σ_op
    (cobarDataOp G R L) (n := n) i

end CobarData

section TwoSidedCobar

variable {G : Comonad C} {R : RightComodule G D} {L : LeftComodule A G}

/-- The two-sided comonadic cobar cosimplicial object.

For a comonad `G` with right comodule `R : C ⥤ D` and left comodule `L : A ⥤ C`, this is the
cosimplicial functor-valued object with degree `n` equal to `R(G^n(L(-)))`. -/
noncomputable def twoSidedCobar (G : Comonad C) (R : RightComodule G D)
    (L : LeftComodule A G) : CosimplicialObject (A ⥤ D) :=
  (cobarDataOp G R L).toSimplicialObject.rightOp ⋙ unopUnop (A ⥤ D)

/-- The degree formula for the two-sided cobar cosimplicial object.

At the simplex of degree `n`, the object is the degree-`n` cobar functor. -/
@[simp] theorem twoSidedCobar_obj_mk (G : Comonad C) (R : RightComodule G D)
    (L : LeftComodule A G) (n : ℕ) :
    (twoSidedCobar G R L).obj (SimplexCategory.mk n) = cobarObj G R L n := by
  have h := SimplicialObject.Data.toSimplicialObject_obj_mk
    (cobarDataOp G R L) n
  simp only [twoSidedCobar, Functor.comp_obj, Functor.rightOp_obj]
  rw [h, cobarDataOp_obj_n]
  rfl

/-- The ordinal-length formula for a two-sided cobar object.

At an ordinal `Δ` in the simplex category, the cobar value is the degree functor indexed by
`Δ.len`. -/
theorem twoSidedCobar_obj (G : Comonad C) (R : RightComodule G D)
    (L : LeftComodule A G) (Δ : SimplexCategory) :
    (twoSidedCobar G R L).obj Δ = cobarObj G R L Δ.len := by
  have h := SimplicialObject.Data.toSimplicialObject_obj
    (cobarDataOp G R L) (Δ := Opposite.op Δ)
  simp only [twoSidedCobar, Functor.comp_obj, Functor.rightOp_obj]
  rw [h]
  rfl

/-- The cofaces of the two-sided cobar cosimplicial object.

A simplex-category coface maps to the corresponding endpoint or comultiplication cobar coface. -/
@[simp] theorem twoSidedCobar_map_δ (G : Comonad C) (R : RightComodule G D)
    (L : LeftComodule A G) {n : ℕ} (i : Fin (n + 2)) :
    (twoSidedCobar G R L).map (SimplexCategory.δ i) =
      cobarCoface (G := G) (R := R) (L := L) n i := by
  have h := SimplicialObject.Data.toSimplicialObject_map_δ
    (cobarDataOp G R L) (n := n) i
  have hδ : (cobarDataOp G R L).δ i =
      (cobarCoface (G := G) (R := R) (L := L) n i).op := rfl
  simp only [twoSidedCobar, Functor.comp_map, Functor.rightOp_map]
  rw [h, hδ]
  rfl

/-- The codegeneracies of the two-sided cobar cosimplicial object.

A simplex-category codegeneracy maps to the corresponding counit cobar codegeneracy. -/
@[simp] theorem twoSidedCobar_map_σ (G : Comonad C) (R : RightComodule G D)
    (L : LeftComodule A G) {n : ℕ} (i : Fin (n + 1)) :
    (twoSidedCobar G R L).map (SimplexCategory.σ i) =
      cobarCodegeneracy (G := G) (R := R) (L := L) n i := by
  have h := SimplicialObject.Data.toSimplicialObject_map_σ
    (cobarDataOp G R L) (n := n) i
  have hσ : (cobarDataOp G R L).σ i =
      (cobarCodegeneracy (G := G) (R := R) (L := L) n i).op := rfl
  simp only [twoSidedCobar, Functor.comp_map, Functor.rightOp_map]
  rw [h, hσ]
  rfl

/-- The pointwise object formula for two-sided cobar.

In degree `n` and at `a ∈ A`, the value is `R(G^n(L(a)))`. -/
@[simp] theorem twoSidedCobar_obj_obj (G : Comonad C) (R : RightComodule G D)
    (L : LeftComodule A G) (n : ℕ) (a : A) :
    ((twoSidedCobar G R L).obj (SimplexCategory.mk n)).obj a =
      R.functor.obj ((comonadPow G n).obj (L.functor.obj a)) := by
  rw [twoSidedCobar_obj_mk]
  rfl

/-- The pointwise carrier-map formula for two-sided cobar.

A morphism `f : a → b` acts in degree `n` by `R.map(G^n.map(L.map(f)))`. -/
@[simp] theorem twoSidedCobar_obj_map (G : Comonad C) (R : RightComodule G D)
    (L : LeftComodule A G) {n : ℕ} {a b : A} (f : a ⟶ b) :
    ((twoSidedCobar G R L).obj (SimplexCategory.mk n)).map f =
      R.functor.map ((comonadPow G n).map (L.functor.map f)) := by
  congr 1

/-- The pointwise coface formula for two-sided cobar.

At a carrier object `a`, the coface component is the corresponding cobar coface component. -/
@[simp] theorem twoSidedCobar_map_δ_app (G : Comonad C) (R : RightComodule G D)
    (L : LeftComodule A G) {n : ℕ} (i : Fin (n + 2)) (a : A) :
    ((twoSidedCobar G R L).map (SimplexCategory.δ i)).app a =
      cobarCofaceApp (G := G) (R := R) (L := L) n i a := by
  rw [twoSidedCobar_map_δ]
  rfl

/-- The pointwise codegeneracy formula for two-sided cobar.

At `a`, codegeneracy `i` is `R` applied to the reversed-position counit insertion at `L(a)`. -/
@[simp] theorem twoSidedCobar_map_σ_app (G : Comonad C) (R : RightComodule G D)
    (L : LeftComodule A G) {n : ℕ} (i : Fin (n + 1)) (a : A) :
    ((twoSidedCobar G R L).map (SimplexCategory.σ i)).app a =
      R.functor.map (cobarEpsilonAtPos G n i (L.functor.obj a)) := by
  rw [twoSidedCobar_map_σ]
  rfl

end TwoSidedCobar

end Comonad

end CategoryTheory
