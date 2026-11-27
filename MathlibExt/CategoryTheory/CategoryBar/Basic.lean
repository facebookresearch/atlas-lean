/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import MathlibExt.AlgebraicTopology.SimplicialObject.ToSimplicial
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Two-sided category bar: objects, faces, degeneracies

For `C : Type u` with `Category.{v} C`, `R : Cᵒᵖ ⥤ Type uR` (right module,
contravariant) and `L : C ⥤ Type uL` (left module, covariant), the degree-`n`
object is `Σ F : ComposableArrows C n, (L.obj F.left × R.obj (op F.right))`.

Chain orientation: `F : Fin (n + 1) ⥤ C` runs `X₀ ⟶ X₁ ⟶ ⋯ ⟶ Xₙ` from left
(`F.left = X₀`, source) to right (`F.right = Xₙ`, target). `L` sits at the
source endpoint, `R` at the target endpoint.

Variance: `L` is covariant (`L.map` pushes forward along `X₀ ⟶ X₁`), `R` is
contravariant (`R.map (op f)` pulls back along `Xₙ ⟶ Xₙ₊₁`).

`n = 0`: `ComposableArrows C 0 ≃ C`, so degree zero is
`Σ x : C, (L.obj x × R.obj (op x))`, pairs of coefficients over the same object.

Faces: `d₀` drops `X₀` and acts by `L` on the first arrow; `d_last` drops `Xₙ₊₁`
and acts by `R` on the last arrow; interior faces compose adjacent arrows and
transport both coefficients along endpoint equalities. Degeneracies insert
identities and transport both coefficients. Faces use the structural
`Fin.cases` then `Fin.lastCases` decomposition so zero, interior
(`q.castSucc.succ`), and last branches compute definitionally.

Provenance: follows the general two-sided bar idea in the nLab two-sided bar
construction overview (`https://ncatlab.org/nlab/show/two-sided+bar+construction`)
and Shulman, *Homotopy limits and colimits and enriched homotopy theory*,
`arXiv:math/0610194`. The Lean construction is the strict ordinary
specialization to a small category `C`, set-valued right/left modules `R`/`L`,
and chains as `ComposableArrows`; no proposition or section number and no exact
sign or formula correspondence beyond this specialization is claimed.

Nonclaims: no functoriality in `C`/`R`/`L`, no comparison with the nerve or
comma/Grothendieck constructions, no contraction or extra degeneracy, and no
Kan–Quillen weak-equivalence or realization consequence yet.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u v uR uL

namespace CategoryTheory

namespace CategoryBar

variable {C : Type u} [Category.{v} C]
variable {R : Cᵒᵖ ⥤ Type uR} {L : C ⥤ Type uL}

/-- Degree-`n` two-sided category bar object. -/
def barObj (C : Type u) [Category.{v} C] (R : Cᵒᵖ ⥤ Type uR) (L : C ⥤ Type uL)
    (n : ℕ) : Type (max u v uL uR) :=
  Σ _F : ComposableArrows C n, (L.obj _F.left × R.obj (op _F.right))

/-- New left after `d₀` is the old second object. -/
private theorem leftδ_zero_eq {n : ℕ} (F : ComposableArrows C (n + 1)) :
    ((nerve C).δ (0 : Fin (n + 2)) F).left = F.obj' 1 := rfl

/-- Left is preserved when the face index is nonzero. -/
private theorem leftδ_of_val_ne_zero {n : ℕ} {i : Fin (n + 2)} (hi : i.val ≠ 0)
    (F : ComposableArrows C (n + 1)) :
    F.left = ((nerve C).δ i F).left := by
  have hi0 : i ≠ 0 := by
    intro h
    apply hi
    rw [h]
    rfl
  change F.obj ⟨0, by omega⟩ = ((nerve C).δ i F).obj (0 : Fin _)
  rw [CategoryTheory.nerve.δ_obj]
  congr 1
  exact (Fin.succAbove_ne_zero_zero hi0).symm

/-- Right is preserved when the face index is not last. -/
private theorem rightδ_of_val_ne_last {n : ℕ} {i : Fin (n + 2)} (hi : i.val ≠ n + 1)
    (F : ComposableArrows C (n + 1)) :
    F.right = ((nerve C).δ i F).right := by
  have hiL : i ≠ Fin.last (n + 1) := by
    intro h
    apply hi
    rw [h]
    simp [Fin.val_last]
  change F.obj ⟨n + 1, by omega⟩ = ((nerve C).δ i F).obj (Fin.last _)
  rw [CategoryTheory.nerve.δ_obj]
  congr 1
  exact (Fin.succAbove_ne_last_last hiL).symm

/-- New right after `d_last` is the old penultimate object. -/
private theorem rightδ_last_eq {n : ℕ} (F : ComposableArrows C (n + 1)) :
    ((nerve C).δ (Fin.last (n + 1)) F).right = F.obj' n := by
  change ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) = F.obj ⟨n, by omega⟩
  rw [CategoryTheory.nerve.δ_obj]
  congr 1
  exact congrFun Fin.succAbove_last _

/-- Degeneracies preserve the left endpoint. -/
private theorem leftσ_eq {n : ℕ} {i : Fin (n + 1)} (F : ComposableArrows C n) :
    F.left = ((nerve C).σ i F).left := by
  change F.obj ⟨0, by omega⟩ = ((nerve C).σ i F).obj (0 : Fin _)
  rw [CategoryTheory.nerve.σ_obj]
  have h : (⟨0, by omega⟩ : Fin _) = i.predAbove (0 : Fin _) :=
    Fin.predAbove_right_zero.symm
  exact congrArg _ h

/-- Degeneracies preserve the right endpoint. -/
private theorem rightσ_eq {n : ℕ} {i : Fin (n + 1)} (F : ComposableArrows C n) :
    F.right = ((nerve C).σ i F).right := by
  change F.obj ⟨n, by omega⟩ = ((nerve C).σ i F).obj (Fin.last _)
  rw [CategoryTheory.nerve.σ_obj]
  congr 1
  exact Fin.predAbove_right_last.symm

/-- Transport a left coefficient forward along an object equality. -/
private def transportL {X Y : C} (h : X = Y) (x : L.obj X) : L.obj Y :=
  cast (congrArg L.obj h) x

/-- Transport a right coefficient forward along an object equality. -/
private def transportR {X Y : C} (h : X = Y) (x : R.obj (op X)) : R.obj (op Y) :=
  cast (congrArg (fun Z => R.obj (op Z)) h) x

/-- Face map: `d₀` uses `L`, `d_last` uses `R`, interior faces transport.

The definition uses outer `Fin.cases` for zero versus successor and inner
`Fin.lastCases` for last versus `q.castSucc`, so the three branches compute
on `0`, `Fin.last _`, and `q.castSucc.succ`. Branch lambdas are inlined so
this public declaration references no private helpers. -/
noncomputable def barδ {n : ℕ} (i : Fin (n + 2)) :
    barObj C R L (n + 1) → barObj C R L n :=
  Fin.cases
    (fun x =>
      match x with
      | ⟨F, l, r⟩ =>
        ⟨(nerve C).δ (0 : Fin (n + 2)) F,
          cast (congrArg L.obj (rfl : F.obj' 1 = ((nerve C).δ (0 : Fin (n + 2)) F).left))
            (L.map (F.map' 0 1) l),
          cast (congrArg (fun Z => R.obj (op Z))
              (by
                change F.obj ⟨n + 1, by omega⟩ =
                  ((nerve C).δ (0 : Fin (n + 2)) F).obj (Fin.last _)
                rw [CategoryTheory.nerve.δ_obj]
                rfl))
            r⟩)
    (fun q x =>
      Fin.lastCases
        (fun x =>
          match x with
          | ⟨F, l, r⟩ =>
            ⟨(nerve C).δ (Fin.last (n + 1)) F,
              cast (congrArg L.obj (by
                  change F.obj ⟨0, by omega⟩ =
                    ((nerve C).δ (Fin.last (n + 1)) F).obj (0 : Fin _)
                  rw [CategoryTheory.nerve.δ_obj]
                  rfl))
                l,
              cast (congrArg (fun Z => R.obj (op Z)) (by
                  have h : ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) =
                      F.obj ⟨n, by omega⟩ := by
                    rw [CategoryTheory.nerve.δ_obj]
                    congr 1
                    exact congrFun Fin.succAbove_last _
                  exact h.symm))
                (R.map (Quiver.Hom.op (F.map' n (n + 1))) r)⟩)
        (fun q' x =>
          match x with
          | ⟨F, l, r⟩ =>
            ⟨(nerve C).δ (q'.castSucc.succ) F,
              cast (congrArg L.obj (by
                  change F.obj ⟨0, by omega⟩ =
                    ((nerve C).δ (q'.castSucc.succ) F).obj (0 : Fin _)
                  rw [CategoryTheory.nerve.δ_obj]
                  rfl))
                l,
              cast (congrArg (fun Z => R.obj (op Z)) (by
                  change F.obj ⟨n + 1, by omega⟩ =
                    ((nerve C).δ (q'.castSucc.succ) F).obj (Fin.last _)
                  rw [CategoryTheory.nerve.δ_obj]
                  congr 1
                  exact (Fin.succAbove_ne_last_last (by
                    apply ne_of_apply_ne Fin.val
                    rw [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
                    have hq := q'.isLt
                    omega)).symm))
                r⟩)
        q x)
    i

/-- Degeneracy map: transports both coefficients. -/
noncomputable def barσ {n : ℕ} (i : Fin (n + 1)) :
    barObj C R L n → barObj C R L (n + 1)
  | ⟨F, l, r⟩ =>
    let F' := (nerve C).σ i F
    have hL : F.left = F'.left := by
      change F.obj ⟨0, by omega⟩ = ((nerve C).σ i F).obj (0 : Fin _)
      rw [CategoryTheory.nerve.σ_obj]
      have h : (⟨0, by omega⟩ : Fin _) = i.predAbove (0 : Fin _) :=
        Fin.predAbove_right_zero.symm
      exact congrArg _ h
    have hR : F.right = F'.right := by
      change F.obj ⟨n, by omega⟩ = ((nerve C).σ i F).obj (Fin.last _)
      rw [CategoryTheory.nerve.σ_obj]
      congr 1
      exact Fin.predAbove_right_last.symm
    ⟨F', cast (congrArg L.obj hL) l,
      cast (congrArg (fun Z => R.obj (op Z)) hR) r⟩

private theorem nerve_δ_comp_δ {n : ℕ} {i j : Fin (n + 2)} (h : i ≤ j)
    (F : ComposableArrows C (n + 2)) :
    (nerve C).δ i ((nerve C).δ j.succ F) = (nerve C).δ j ((nerve C).δ i.castSucc F) :=
  SSet.δ_comp_δ_apply (S := nerve C) h F

private theorem nerve_δ_comp_σ_of_le {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : i ≤ j.castSucc) (F : ComposableArrows C (n + 1)) :
    (nerve C).δ i.castSucc ((nerve C).σ j.succ F) =
      (nerve C).σ j ((nerve C).δ i F) :=
  SSet.δ_comp_σ_of_le_apply (S := nerve C) h F

private theorem nerve_δ_comp_σ_self {n : ℕ} {i : Fin (n + 1)}
    (F : ComposableArrows C n) :
    (nerve C).δ i.castSucc ((nerve C).σ i F) = F :=
  SSet.δ_comp_σ_self_apply (S := nerve C) i F

private theorem nerve_δ_comp_σ_succ {n : ℕ} {i : Fin (n + 1)}
    (F : ComposableArrows C n) :
    (nerve C).δ i.succ ((nerve C).σ i F) = F :=
  SSet.δ_comp_σ_succ_apply (S := nerve C) i F

private theorem nerve_δ_comp_σ_of_gt {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : j.castSucc < i) (F : ComposableArrows C (n + 1)) :
    (nerve C).δ i.succ ((nerve C).σ j.castSucc F) =
      (nerve C).σ j ((nerve C).δ i F) :=
  SSet.δ_comp_σ_of_gt_apply (S := nerve C) h F

private theorem nerve_σ_comp_σ {n : ℕ} {i j : Fin (n + 1)} (h : i ≤ j)
    (F : ComposableArrows C n) :
    (nerve C).σ i.castSucc ((nerve C).σ j F) =
      (nerve C).σ j.succ ((nerve C).σ i F) :=
  SSet.σ_comp_σ_apply (S := nerve C) h F

/-- Two-step left transport collapses to a direct transport. -/
private theorem transportL_trans {X Y Z : C} (h1 : X = Y) (h2 : Y = Z)
    (x : L.obj X) (h3 : X = Z) :
    transportL h2 (transportL h1 x) = transportL h3 x := by
  subst h1
  subst h2
  rfl

/-- Two-step right transport collapses to a direct transport. -/
private theorem transportR_trans {X Y Z : C} (h1 : X = Y) (h2 : Y = Z)
    (x : R.obj (op X)) (h3 : X = Z) :
    transportR h2 (transportR h1 x) = transportR h3 x := by
  subst h1
  subst h2
  rfl

/-- A left action commutes past a domain transport via `eqToHom`. -/
private theorem transportL_map {X Y Z : C} (h : X = Y) (f : Y ⟶ Z) (x : L.obj X) :
    L.map f (transportL h x) = L.map (eqToHom h ≫ f) x := by
  subst h
  simp [transportL]

/-- A right action commutes past a codomain transport via `eqToHom`. -/
private theorem transportR_map {X Y W : C} (h : X = Y) (f : W ⟶ Y)
    (x : R.obj (op X)) :
    R.map f.op (transportR h x) = R.map (f ≫ eqToHom h.symm).op x := by
  subst h
  simp [transportR]

/-- Post-interior-face second-last object.

For `F : ComposableArrows C (n + 2)` and interior `qi : Fin n`, let
`p : Fin (n + 3)` be the interior index and `G : ComposableArrows C (n + 1)`
with `hG : G = (nerve C).δ p F`.
Then the second-last object of `G` is the second-last object of `F`.
This isolates the interior--last endpoint from the actual face chain;
in particular the relevant endpoint is `G.obj' n`, not an assumed
`F.obj k.succ` shape. -/
private theorem postFace_secondLast_obj {n : ℕ}
    (F : ComposableArrows C (n + 2)) (qi : Fin n)
    (G : ComposableArrows C (n + 1))
    (hG : G = (nerve C).δ (((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ)) F) :
    G.obj' n (by omega) = F.obj' (n + 1) (by omega) := by
  set p : Fin (n + 3) :=
    ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ)
  set k : Fin (n + 2) := ⟨n, by omega⟩
  have hqi : qi.val < n := qi.isLt
  have hpk : p ≤ k.castSucc := by
    change qi.val + 1 ≤ n
    omega
  have hSucc : p.succAbove k = k.succ :=
    Fin.succAbove_of_le_castSucc p k hpk
  have hObj : G.obj k = F.obj k.succ := by
    rw [hG, CategoryTheory.nerve.δ_obj, hSucc]
  exact hObj

/-- Structural trichotomy for `Fin (n + 2)` indices. -/
private theorem fin_tri {n : ℕ} (i : Fin (n + 2)) :
    i = 0 ∨ (∃ q : Fin n, i = q.castSucc.succ) ∨ i = Fin.last (n + 1) := by
  refine Fin.cases ?_ ?_ i
  · exact Or.inl rfl
  · intro q
    refine Fin.lastCases ?_ ?_ q
    · exact Or.inr (Or.inr rfl)
    · intro q'
      exact Or.inr (Or.inl ⟨q', rfl⟩)

/-- Zero versus successor split for `Fin (n + 1)`. -/
private theorem fin_zero_succ {n : ℕ} (i : Fin (n + 1)) :
    i = 0 ∨ ∃ q : Fin n, i = q.succ := by
  refine Fin.cases ?_ ?_ i
  · exact Or.inl rfl
  · intro q
    exact Or.inr ⟨q, rfl⟩

/-- Last versus `castSucc` split for `Fin (n + 1)`. -/
private theorem fin_last_castSucc {n : ℕ} (i : Fin (n + 1)) :
    i = Fin.last n ∨ ∃ q : Fin n, i = q.castSucc := by
  refine Fin.lastCases ?_ ?_ i
  · exact Or.inl rfl
  · intro q
    exact Or.inr ⟨q, rfl⟩

/-- Computation: `barδ` at `0` is the left-action branch. -/
theorem barδ_zero_eq {n : ℕ} (x : barObj C R L (n + 1)) :
    barδ (0 : Fin (n + 2)) x =
      match x with
      | ⟨F, l, r⟩ =>
        ⟨(nerve C).δ (0 : Fin (n + 2)) F,
          cast (congrArg L.obj (rfl : F.obj' 1 = ((nerve C).δ (0 : Fin (n + 2)) F).left))
            (L.map (F.map' 0 1) l),
          cast (congrArg (fun Z => R.obj (op Z))
              (by
                change F.obj ⟨n + 1, by omega⟩ =
                  ((nerve C).δ (0 : Fin (n + 2)) F).obj (Fin.last _)
                rw [CategoryTheory.nerve.δ_obj]
                rfl))
            r⟩ := by
  obtain ⟨F, l, r⟩ := x
  unfold barδ
  rw [Fin.cases_zero]

/-- Computation: `barδ` at `last` is the right-action branch. -/
theorem barδ_last_eq {n : ℕ} (x : barObj C R L (n + 1)) :
    barδ (Fin.last (n + 1)) x =
      match x with
      | ⟨F, l, r⟩ =>
        ⟨(nerve C).δ (Fin.last (n + 1)) F,
          cast (congrArg L.obj (by
              change F.obj ⟨0, by omega⟩ =
                ((nerve C).δ (Fin.last (n + 1)) F).obj (0 : Fin _)
              rw [CategoryTheory.nerve.δ_obj]
              rfl))
            l,
          cast (congrArg (fun Z => R.obj (op Z)) (by
              have h : ((nerve C).δ (Fin.last (n + 1)) F).obj (Fin.last _) =
                  F.obj ⟨n, by omega⟩ := by
                rw [CategoryTheory.nerve.δ_obj]
                congr 1
                exact congrFun Fin.succAbove_last _
              exact h.symm))
            (R.map (Quiver.Hom.op (F.map' n (n + 1))) r)⟩ := by
  have hEq : Fin.last (n + 1) = (Fin.last n).succ := rfl
  conv_lhs => rw [hEq]
  obtain ⟨F, l, r⟩ := x
  unfold barδ
  rw [Fin.cases_succ, Fin.lastCases_last]

/-- Computation: `barδ` at `q.castSucc.succ` is the interior transport branch. -/
theorem barδ_castSucc_succ_eq {n : ℕ} (q : Fin n) (x : barObj C R L (n + 1)) :
    barδ (q.castSucc.succ) x =
      match x with
      | ⟨F, l, r⟩ =>
        ⟨(nerve C).δ (q.castSucc.succ) F,
          cast (congrArg L.obj (by
              change F.obj ⟨0, by omega⟩ =
                ((nerve C).δ (q.castSucc.succ) F).obj (0 : Fin _)
              rw [CategoryTheory.nerve.δ_obj]
              rfl))
            l,
          cast (congrArg (fun Z => R.obj (op Z)) (by
              change F.obj ⟨n + 1, by omega⟩ =
                ((nerve C).δ (q.castSucc.succ) F).obj (Fin.last _)
              rw [CategoryTheory.nerve.δ_obj]
              congr 1
              exact (Fin.succAbove_ne_last_last (by
                apply ne_of_apply_ne Fin.val
                rw [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
                have hq := q.isLt
                omega)).symm))
            r⟩ := by
  obtain ⟨F, l, r⟩ := x
  unfold barδ
  rw [Fin.cases_succ, Fin.lastCases_castSucc]

/- Implementation laws assembling `categoryBarData`.

These six identities are the public proof witnesses for the simplicial data.
They are kept in this namespace (not as stable API) so the public
`categoryBarData` literal has a module-safe dependency DAG. Transport helpers
stay private and are not re-exposed here. -/
namespace BarLaws

/-- Face-face identity over the six live index cases. -/
theorem δ_comp_δ {n : ℕ} {i j : Fin (n + 2)} (h : i ≤ j)
    (x : barObj C R L (n + 2)) :
    barδ (R := R) (L := L) i (barδ j.succ x) =
      barδ (R := R) (L := L) j (barδ i.castSucc x) := by
  obtain ⟨F, l, r⟩ := x
  have hi := fin_tri (n := n) i
  have hj := fin_tri (n := n) j
  rcases hi with rfl | ⟨qi, rfl⟩ | rfl <;> rcases hj with rfl | ⟨qj, rfl⟩ | rfl
  · -- 0, 0: two left actions cohere via `L.map_comp`.
    set y : barObj C R L (n + 2) := ⟨F, l, r⟩ with hy
    have hChain := nerve_δ_comp_δ (n := n) (i := (0 : Fin (n + 2))) (j := (0 : Fin (n + 2)))
      (by omega) F
    have hJs : (0 : Fin (n + 2)).succ = (0 : Fin (n + 1)).castSucc.succ := by
      apply Fin.ext
      simp
    have hIc : (0 : Fin (n + 2)).castSucc = (0 : Fin (n + 3)) := by
      apply Fin.ext
      simp
    have hComp : F.map' 0 2 = F.map' 0 1 ≫ F.map' 1 2 :=
      ComposableArrows.map'_comp F 0 1 2
    rw [hJs, hIc] at hChain ⊢
    -- Typed inner-face equalities: both inner computations are stated with the
    -- chain binder at the canonical `ComposableArrows C (n + 2)` degree, so the
    -- raw `F` is never substituted into a dependent `n + 1 + 1` motive and no
    -- degree is rewritten inside the dependent goal.
    have hInnerL : barδ ((0 : Fin (n + 1)).castSucc.succ) y =
        ⟨(nerve C).δ ((0 : Fin (n + 1)).castSucc.succ) F,
          transportL
            (leftδ_of_val_ne_zero (n := n + 1)
              (i := (0 : Fin (n + 1)).castSucc.succ)
              (by rw [Fin.val_succ, Fin.val_castSucc, Fin.val_zero]; omega) F) l,
          transportR
            (rightδ_of_val_ne_last (n := n + 1)
              (i := (0 : Fin (n + 1)).castSucc.succ)
              (by rw [Fin.val_succ, Fin.val_castSucc, Fin.val_zero]; omega) F) r⟩ := by
      rw [barδ_castSucc_succ_eq (n := n + 1) (0 : Fin (n + 1)) y, hy]
      rfl
    have hInnerR : barδ (0 : Fin (n + 3)) y =
        ⟨(nerve C).δ (0 : Fin (n + 3)) F,
          transportL (leftδ_zero_eq (n := n + 1) F).symm (L.map (F.map' 0 1) l),
          transportR
            (rightδ_of_val_ne_last (n := n + 1)
              (i := (0 : Fin (n + 3)))
              (by rw [Fin.val_zero]; omega) F) r⟩ := by
      rw [barδ_zero_eq (n := n + 1) y, hy]
      rfl
    set zL : barObj C R L (n + 1) :=
      ⟨(nerve C).δ ((0 : Fin (n + 1)).castSucc.succ) F,
        transportL
          (leftδ_of_val_ne_zero (n := n + 1)
            (i := (0 : Fin (n + 1)).castSucc.succ)
            (by rw [Fin.val_succ, Fin.val_castSucc, Fin.val_zero]; omega) F) l,
        transportR
          (rightδ_of_val_ne_last (n := n + 1)
            (i := (0 : Fin (n + 1)).castSucc.succ)
            (by rw [Fin.val_succ, Fin.val_castSucc, Fin.val_zero]; omega) F) r⟩ with hzLdef
    set zR : barObj C R L (n + 1) :=
      ⟨(nerve C).δ (0 : Fin (n + 3)) F,
        transportL (leftδ_zero_eq (n := n + 1) F).symm (L.map (F.map' 0 1) l),
        transportR
          (rightδ_of_val_ne_last (n := n + 1)
            (i := (0 : Fin (n + 3)))
            (by rw [Fin.val_zero]; omega) F) r⟩ with hzRdef
    have hzL : barδ ((0 : Fin (n + 1)).castSucc.succ) y = zL := by
      rw [hzLdef]
      exact hInnerL
    have hzR : barδ (0 : Fin (n + 3)) y = zR := by
      rw [hzRdef]
      exact hInnerR
    rw [hzL, hzR]
    -- Fully explicit outer endpoint equalities mentioning the direct inner
    -- chains, used in every outer transport so no placeholder is needed.
    have hLInnerLeft : F.left = ((nerve C).δ ((0 : Fin (n + 1)).castSucc.succ) F).left :=
      leftδ_of_val_ne_zero (n := n + 1)
        (i := (0 : Fin (n + 1)).castSucc.succ)
        (by rw [Fin.val_succ, Fin.val_castSucc, Fin.val_zero]; omega) F
    have hLInnerRight : F.right = ((nerve C).δ ((0 : Fin (n + 1)).castSucc.succ) F).right :=
      rightδ_of_val_ne_last (n := n + 1)
        (i := (0 : Fin (n + 1)).castSucc.succ)
        (by rw [Fin.val_succ, Fin.val_castSucc, Fin.val_zero]; omega) F
    have hRInnerLeft : F.obj' 1 = ((nerve C).δ (0 : Fin (n + 3)) F).left :=
      (leftδ_zero_eq (n := n + 1) F).symm
    have hRInnerRight : F.right = ((nerve C).δ (0 : Fin (n + 3)) F).right :=
      rightδ_of_val_ne_last (n := n + 1) (i := (0 : Fin (n + 3))) (by rw [Fin.val_zero]; omega) F
    have hLOuterLeft :=
      (leftδ_zero_eq (n := n) ((nerve C).δ ((0 : Fin (n + 1)).castSucc.succ) F)).symm
    have hLOuterRight :
        ((nerve C).δ ((0 : Fin (n + 1)).castSucc.succ) F).right =
          ((nerve C).δ (0 : Fin (n + 2))
            ((nerve C).δ ((0 : Fin (n + 1)).castSucc.succ) F)).right :=
      rightδ_of_val_ne_last (n := n) (i := (0 : Fin (n + 2)))
        (Nat.zero_ne_add_one n) ((nerve C).δ ((0 : Fin (n + 1)).castSucc.succ) F)
    have hROuterLeft := (leftδ_zero_eq (n := n) ((nerve C).δ (0 : Fin (n + 3)) F)).symm
    have hROuterRight :
        ((nerve C).δ (0 : Fin (n + 3)) F).right =
          ((nerve C).δ (0 : Fin (n + 2)) ((nerve C).δ (0 : Fin (n + 3)) F)).right :=
      rightδ_of_val_ne_last (n := n) (i := (0 : Fin (n + 2)))
        (Nat.zero_ne_add_one n) ((nerve C).δ (0 : Fin (n + 3)) F)
    have hOuterL : barδ (0 : Fin (n + 2)) zL =
        ⟨(nerve C).δ (0 : Fin (n + 2)) ((nerve C).δ ((0 : Fin (n + 1)).castSucc.succ) F),
          transportL hLOuterLeft (L.map (F.map' 0 2) (transportL hLInnerLeft l)),
          transportR hLOuterRight (transportR hLInnerRight r)⟩ := by
      rw [barδ_zero_eq (n := n) zL, hzLdef]
      rfl
    have hOuterR : barδ (0 : Fin (n + 2)) zR =
        ⟨(nerve C).δ (0 : Fin (n + 2)) ((nerve C).δ (0 : Fin (n + 3)) F),
          transportL hROuterLeft
            (L.map (F.map' 1 2) (transportL hRInnerLeft (L.map (F.map' 0 1) l))),
          transportR hROuterRight (transportR hRInnerRight r)⟩ := by
      rw [barδ_zero_eq (n := n) zR, hzRdef]
      rfl
    have hRight :
        F.right =
          ((nerve C).δ (0 : Fin (n + 2))
            ((nerve C).δ ((0 : Fin (n + 1)).castSucc.succ) F)).right :=
      hLInnerRight.trans hLOuterRight
    have hLeftAux : ∀ {X0 X1 X2 Z1 Z2 : C} (x : L.obj X0)
        (e1 : X0 = X0) (f02 : X0 ⟶ X2) (e2 : X2 = Z1)
        (f01 : X0 ⟶ X1) (e3 : X1 = X1) (f12 : X1 ⟶ X2) (e4 : X2 = Z2)
        (hT : Z1 = Z2) (hComp : f02 = f01 ≫ f12),
        transportL e2 (L.map f02 (transportL e1 x)) =
        cast (congrArg L.obj hT).symm
          (transportL e4 (L.map f12 (transportL e3 (L.map f01 x)))) := by
      intro X0 X1 X2 Z1 Z2 x e1 f02 e2 f01 e3 f12 e4 hT hComp
      cases e1
      cases e3
      cases e2
      cases hT
      cases e4
      rw [hComp, L.map_comp]
      rfl
    have hCoeffHEq :
        (transportL hLOuterLeft (L.map (F.map' 0 2) (transportL hLInnerLeft l)),
          transportR hLOuterRight (transportR hLInnerRight r)) ≍
        (transportL hROuterLeft
            (L.map (F.map' 1 2) (transportL hRInnerLeft (L.map (F.map' 0 1) l))),
          transportR hROuterRight (transportR hRInnerRight r)) := by
      cases hChain
      have hLeft :
          transportL hLOuterLeft (L.map (F.map' 0 2) (transportL hLInnerLeft l)) =
            transportL hROuterLeft
              (L.map (F.map' 1 2)
                (transportL hRInnerLeft (L.map (F.map' 0 1) l))) :=
        hLeftAux l hLInnerLeft (F.map' 0 2) hLOuterLeft (F.map' 0 1) hRInnerLeft
          (F.map' 1 2) hROuterLeft rfl hComp
      apply heq_of_eq
      apply Prod.ext
      · exact hLeft
      · -- Right coefficients: pure endpoint transports cohere.
        -- Both outer results are already in transport form, so the collapses
        -- apply directly without restating raw casts.
        rw [transportR_trans hLInnerRight hLOuterRight r hRight,
          transportR_trans hRInnerRight hROuterRight r hRight]
        rfl
    rw [hOuterL, hOuterR]
    exact Sigma.ext hChain hCoeffHEq
  · -- 0, interior: one left action each side, transports agree.
    set y : barObj C R L (n + 2) := ⟨F, l, r⟩ with hy
    have hChain := nerve_δ_comp_δ (n := n) (i := (0 : Fin (n + 2)))
      (j := qj.castSucc.succ) h F
    have hJs : (qj.castSucc.succ).succ = (⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ := by
      apply Fin.ext
      simp [Fin.val_succ, Fin.val_castSucc]
    have hIc : (0 : Fin (n + 2)).castSucc = (0 : Fin (n + 3)) := by
      apply Fin.ext
      simp
    rw [hJs, hIc] at hChain ⊢
    have hqLt : qj.val < n := qj.isLt
    have hLInnerLeft : F.left =
        ((nerve C).δ ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ) F).left :=
      leftδ_of_val_ne_zero (n := n + 1)
        (i := ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ))
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega) F
    have hLInnerRight : F.right =
        ((nerve C).δ ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ) F).right :=
      rightδ_of_val_ne_last (n := n + 1)
        (i := ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ))
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega) F
    have hRInnerLeft : F.obj' 1 = ((nerve C).δ (0 : Fin (n + 3)) F).left :=
      (leftδ_zero_eq (n := n + 1) F).symm
    have hRInnerRight : F.right = ((nerve C).δ (0 : Fin (n + 3)) F).right :=
      rightδ_of_val_ne_last (n := n + 1) (i := (0 : Fin (n + 3)))
        (by rw [Fin.val_zero]; omega) F
    have hInnerL : barδ ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ) y =
        ⟨(nerve C).δ ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ) F,
          transportL hLInnerLeft l, transportR hLInnerRight r⟩ := by
      rw [barδ_castSucc_succ_eq (n := n + 1)
        (⟨qj.val + 1, by omega⟩ : Fin (n + 1)) y, hy]
      rfl
    have hInnerR : barδ (0 : Fin (n + 3)) y =
        ⟨(nerve C).δ (0 : Fin (n + 3)) F,
          transportL hRInnerLeft (L.map (F.map' 0 1) l),
          transportR hRInnerRight r⟩ := by
      rw [barδ_zero_eq (n := n + 1) y, hy]
      rfl
    set zL : barObj C R L (n + 1) :=
      ⟨(nerve C).δ ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ) F,
        transportL hLInnerLeft l, transportR hLInnerRight r⟩ with hzLdef
    set zR : barObj C R L (n + 1) :=
      ⟨(nerve C).δ (0 : Fin (n + 3)) F,
        transportL hRInnerLeft (L.map (F.map' 0 1) l),
        transportR hRInnerRight r⟩ with hzRdef
    have hzL : barδ ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ) y = zL := by
      rw [hzLdef]
      exact hInnerL
    have hzR : barδ (0 : Fin (n + 3)) y = zR := by
      rw [hzRdef]
      exact hInnerR
    rw [hzL, hzR]
    have hLOuterLeft := (leftδ_zero_eq (n := n)
      ((nerve C).δ ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ) F)).symm
    have hLOuterRight :
        ((nerve C).δ ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ) F).right =
        ((nerve C).δ (0 : Fin (n + 2))
          ((nerve C).δ ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ) F)).right :=
      rightδ_of_val_ne_last (n := n) (i := (0 : Fin (n + 2)))
        (Nat.zero_ne_add_one n)
        ((nerve C).δ ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ) F)
    have hROuterLeft : ((nerve C).δ (0 : Fin (n + 3)) F).left =
        ((nerve C).δ (qj.castSucc.succ) ((nerve C).δ (0 : Fin (n + 3)) F)).left :=
      leftδ_of_val_ne_zero (n := n) (i := qj.castSucc.succ)
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega)
        ((nerve C).δ (0 : Fin (n + 3)) F)
    have hROuterRight : ((nerve C).δ (0 : Fin (n + 3)) F).right =
        ((nerve C).δ (qj.castSucc.succ) ((nerve C).δ (0 : Fin (n + 3)) F)).right :=
      rightδ_of_val_ne_last (n := n) (i := qj.castSucc.succ)
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega)
        ((nerve C).δ (0 : Fin (n + 3)) F)
    have hOuterL : barδ (0 : Fin (n + 2)) zL =
        ⟨(nerve C).δ (0 : Fin (n + 2))
          ((nerve C).δ ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ) F),
          transportL hLOuterLeft (L.map (F.map' 0 1) (transportL hLInnerLeft l)),
          transportR hLOuterRight (transportR hLInnerRight r)⟩ := by
      rw [barδ_zero_eq (n := n) zL, hzLdef]
      rfl
    have hOuterR : barδ (qj.castSucc.succ) zR =
        ⟨(nerve C).δ (qj.castSucc.succ) ((nerve C).δ (0 : Fin (n + 3)) F),
          transportL hROuterLeft (transportL hRInnerLeft (L.map (F.map' 0 1) l)),
          transportR hROuterRight (transportR hRInnerRight r)⟩ := by
      rw [barδ_castSucc_succ_eq (n := n) qj zR, hzRdef]
      rfl
    have hRight : F.right =
        ((nerve C).δ (0 : Fin (n + 2))
          ((nerve C).δ ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ) F)).right :=
      hLInnerRight.trans hLOuterRight
    have hFinalL :
        ((nerve C).δ (0 : Fin (n + 2))
            ((nerve C).δ ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ) F)).left =
          ((nerve C).δ (qj.castSucc.succ) ((nerve C).δ (0 : Fin (n + 3)) F)).left :=
      congrArg (fun G => G.left) hChain
    have hFinalR :
        ((nerve C).δ (0 : Fin (n + 2))
            ((nerve C).δ ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ) F)).right =
          ((nerve C).δ (qj.castSucc.succ) ((nerve C).δ (0 : Fin (n + 3)) F)).right :=
      congrArg (fun G => G.right) hChain
    have hPairAux :
        ∀ {X0 XM ZL1 ZL2 Y0 YR1 ZR1 YR2 ZR2 : C} (x : L.obj X0) (y : R.obj (op Y0))
          (f : X0 ⟶ XM)
        (e1 : X0 = X0) (e2 : XM = ZL1) (e3 : XM = XM) (e4 : XM = ZL2) (hT : ZL1 = ZL2)
        (er1 : Y0 = YR1) (er2 : YR1 = ZR1) (er3 : Y0 = YR2) (er4 : YR2 = ZR2) (hTR : ZR1 = ZR2),
        (transportL e2 (L.map f (transportL e1 x)), transportR er2 (transportR er1 y)) =
        cast (by cases hT; cases hTR; rfl)
          (transportL e4 (transportL e3 (L.map f x)),
            transportR er4 (transportR er3 y)) := by
      intro X0 XM ZL1 ZL2 Y0 YR1 ZR1 YR2 ZR2 x y f e1 e2 e3 e4 hT er1 er2 er3 er4 hTR
      cases e1
      cases e3
      cases e2
      cases hT
      cases e4
      cases er1
      cases er3
      cases er2
      cases hTR
      cases er4
      rfl
    have hEq :=
      hPairAux l r (F.map' 0 1) hLInnerLeft hLOuterLeft hRInnerLeft hROuterLeft
        hFinalL hLInnerRight hLOuterRight hRInnerRight hROuterRight hFinalR
    have hCoeffHEq :
        (transportL hLOuterLeft (L.map (F.map' 0 1) (transportL hLInnerLeft l)),
          transportR hLOuterRight (transportR hLInnerRight r)) ≍
        (transportL hROuterLeft (transportL hRInnerLeft (L.map (F.map' 0 1) l)),
          transportR hROuterRight (transportR hRInnerRight r)) :=
      hEq ▸ cast_heq _ _
    rw [hOuterL, hOuterR]
    exact Sigma.ext hChain hCoeffHEq
  · -- 0, last: left and right actions commute via transports.
    set y : barObj C R L (n + 2) := ⟨F, l, r⟩ with hy
    have hChain := nerve_δ_comp_δ (n := n) (i := (0 : Fin (n + 2)))
      (j := Fin.last (n + 1)) h F
    have hJs : (Fin.last (n + 1)).succ = Fin.last (n + 2) := rfl
    have hIc : (0 : Fin (n + 2)).castSucc = (0 : Fin (n + 3)) := by
      apply Fin.ext
      simp
    rw [hJs, hIc] at hChain ⊢
    have hLInnerLeft : F.left =
        ((nerve C).δ (Fin.last (n + 2)) F).left :=
      leftδ_of_val_ne_zero (n := n + 1)
        (i := Fin.last (n + 2))
        (by rw [Fin.val_last]; omega) F
    have hLInnerRight : F.obj' (n + 1) =
        ((nerve C).δ (Fin.last (n + 2)) F).right :=
      (rightδ_last_eq (n := n + 1) F).symm
    have hRInnerLeft : F.obj' 1 = ((nerve C).δ (0 : Fin (n + 3)) F).left :=
      (leftδ_zero_eq (n := n + 1) F).symm
    have hRInnerRight : F.right = ((nerve C).δ (0 : Fin (n + 3)) F).right :=
      rightδ_of_val_ne_last (n := n + 1) (i := (0 : Fin (n + 3)))
        (by rw [Fin.val_zero]; omega) F
    have hInnerL : barδ (Fin.last (n + 2)) y =
        ⟨(nerve C).δ (Fin.last (n + 2)) F,
          transportL hLInnerLeft l,
          transportR hLInnerRight (R.map (Quiver.Hom.op (F.map' (n + 1) (n + 2))) r)⟩ := by
      rw [barδ_last_eq (n := n + 1) y, hy]
      rfl
    have hInnerR : barδ (0 : Fin (n + 3)) y =
        ⟨(nerve C).δ (0 : Fin (n + 3)) F,
          transportL hRInnerLeft (L.map (F.map' 0 1) l),
          transportR hRInnerRight r⟩ := by
      rw [barδ_zero_eq (n := n + 1) y, hy]
      rfl
    set zL : barObj C R L (n + 1) :=
      ⟨(nerve C).δ (Fin.last (n + 2)) F,
        transportL hLInnerLeft l,
        transportR hLInnerRight (R.map (Quiver.Hom.op (F.map' (n + 1) (n + 2))) r)⟩ with hzLdef
    set zR : barObj C R L (n + 1) :=
      ⟨(nerve C).δ (0 : Fin (n + 3)) F,
        transportL hRInnerLeft (L.map (F.map' 0 1) l),
        transportR hRInnerRight r⟩ with hzRdef
    have hzL : barδ (Fin.last (n + 2)) y = zL := by
      rw [hzLdef]
      exact hInnerL
    have hzR : barδ (0 : Fin (n + 3)) y = zR := by
      rw [hzRdef]
      exact hInnerR
    rw [hzL, hzR]
    have hLOuterLeft :=
      (leftδ_zero_eq (n := n) ((nerve C).δ (Fin.last (n + 2)) F)).symm
    have hLOuterRight :=
      rightδ_of_val_ne_last (n := n) (i := (0 : Fin (n + 2)))
        (Nat.zero_ne_add_one n)
        ((nerve C).δ (Fin.last (n + 2)) F)
    have hROuterLeft :=
      leftδ_of_val_ne_zero (n := n) (i := Fin.last (n + 1))
        (by rw [Fin.val_last]; omega)
        ((nerve C).δ (0 : Fin (n + 3)) F)
    have hROuterRight :=
      (rightδ_last_eq (n := n) ((nerve C).δ (0 : Fin (n + 3)) F)).symm
    have hOuterL : barδ (0 : Fin (n + 2)) zL =
        ⟨(nerve C).δ (0 : Fin (n + 2)) ((nerve C).δ (Fin.last (n + 2)) F),
          transportL hLOuterLeft (L.map (F.map' 0 1) (transportL hLInnerLeft l)),
          transportR hLOuterRight
            (transportR hLInnerRight (R.map (Quiver.Hom.op (F.map' (n + 1) (n + 2))) r))⟩ := by
      rw [barδ_zero_eq (n := n) zL, hzLdef]
      rfl
    have hOuterR : barδ (Fin.last (n + 1)) zR =
        ⟨(nerve C).δ (Fin.last (n + 1)) ((nerve C).δ (0 : Fin (n + 3)) F),
          transportL hROuterLeft (transportL hRInnerLeft (L.map (F.map' 0 1) l)),
          transportR hROuterRight
            (R.map (Quiver.Hom.op (F.map' (n + 1) (n + 2))) (transportR hRInnerRight r))⟩ := by
      rw [barδ_last_eq (n := n) zR, hzRdef]
      rfl
    have hFinalL : ((nerve C).δ (0 : Fin (n + 2)) ((nerve C).δ (Fin.last (n + 2)) F)).left =
        ((nerve C).δ (Fin.last (n + 1)) ((nerve C).δ (0 : Fin (n + 3)) F)).left :=
      congrArg (fun G => G.left) hChain
    have hFinalR : ((nerve C).δ (0 : Fin (n + 2)) ((nerve C).δ (Fin.last (n + 2)) F)).right =
        ((nerve C).δ (Fin.last (n + 1)) ((nerve C).δ (0 : Fin (n + 3)) F)).right :=
      congrArg (fun G => G.right) hChain
    have hPairAux : ∀ {X0 XM ZL1 ZL2 Y0 YM YR1 ZR1 ZR2 : C} (x : L.obj X0) (y : R.obj (op Y0))
        (fL : X0 ⟶ XM) (gR : op Y0 ⟶ op YM)
        (e1 : X0 = X0) (e2 : XM = ZL1) (e3 : XM = XM) (e4 : XM = ZL2) (hT : ZL1 = ZL2)
        (er1 : YM = YR1) (er2 : YR1 = ZR1) (er3 : Y0 = Y0) (er4 : YM = ZR2) (hTR : ZR1 = ZR2),
        (transportL e2 (L.map fL (transportL e1 x)),
          transportR er2 (transportR er1 (R.map gR y))) =
        cast (by cases hT; cases hTR; rfl)
          (transportL e4 (transportL e3 (L.map fL x)),
            transportR er4 (R.map gR (transportR er3 y))) := by
      intro X0 XM ZL1 ZL2 Y0 YM YR1 ZR1 ZR2 x y fL gR e1 e2 e3 e4 hT er1 er2 er3 er4 hTR
      cases e1
      cases e3
      cases e2
      cases hT
      cases e4
      cases er3
      cases er1
      cases er2
      cases hTR
      cases er4
      rfl
    have hEq := hPairAux l r (F.map' 0 1) (Quiver.Hom.op (F.map' (n + 1) (n + 2)))
      hLInnerLeft hLOuterLeft hRInnerLeft hROuterLeft hFinalL
      hLInnerRight hLOuterRight hRInnerRight hROuterRight hFinalR
    have hCoeffHEq :
        (transportL hLOuterLeft (L.map (F.map' 0 1) (transportL hLInnerLeft l)),
          transportR hLOuterRight
            (transportR hLInnerRight (R.map (Quiver.Hom.op (F.map' (n + 1) (n + 2))) r))) ≍
        (transportL hROuterLeft (transportL hRInnerLeft (L.map (F.map' 0 1) l)),
          transportR hROuterRight
            (R.map (Quiver.Hom.op (F.map' (n + 1) (n + 2))) (transportR hRInnerRight r))) :=
      hEq ▸ cast_heq _ _
    rw [hOuterL, hOuterR]
    exact Sigma.ext hChain hCoeffHEq
  · -- interior, 0 impossible by `i ≤ j`.
    have hval : (qi.castSucc.succ : Fin (n + 2)).val ≤ (0 : Fin (n + 2)).val := h
    rw [Fin.val_succ, Fin.val_castSucc, Fin.val_zero] at hval
    have hqi := qi.isLt
    omega
  · -- interior, interior: transports only.
    set y : barObj C R L (n + 2) := ⟨F, l, r⟩ with hy
    have hChain := nerve_δ_comp_δ (n := n) (i := qi.castSucc.succ)
      (j := qj.castSucc.succ) h F
    have hJs : (qj.castSucc.succ).succ =
        (⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ := by
      apply Fin.ext
      simp [Fin.val_succ, Fin.val_castSucc]
    have hIc : (qi.castSucc.succ).castSucc =
        (⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ := by
      apply Fin.ext
      simp [Fin.val_castSucc, Fin.val_succ]
    rw [hJs, hIc] at hChain ⊢
    have hLInnerLeft : F.left =
        ((nerve C).δ ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ) F).left :=
      leftδ_of_val_ne_zero (n := n + 1)
        (i := ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ))
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega) F
    have hLInnerRight : F.right =
        ((nerve C).δ ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ) F).right :=
      rightδ_of_val_ne_last (n := n + 1)
        (i := ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ))
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega) F
    have hRInnerLeft : F.left =
        ((nerve C).δ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ) F).left :=
      leftδ_of_val_ne_zero (n := n + 1)
        (i := ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ))
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega) F
    have hRInnerRight : F.right =
        ((nerve C).δ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ) F).right :=
      rightδ_of_val_ne_last (n := n + 1)
        (i := ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ))
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega) F
    have hInnerL : barδ ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ) y =
        ⟨(nerve C).δ ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ) F,
          transportL hLInnerLeft l, transportR hLInnerRight r⟩ := by
      rw [barδ_castSucc_succ_eq (n := n + 1)
        (⟨qj.val + 1, by omega⟩ : Fin (n + 1)) y, hy]
      rfl
    have hInnerR : barδ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ) y =
        ⟨(nerve C).δ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ) F,
          transportL hRInnerLeft l, transportR hRInnerRight r⟩ := by
      rw [barδ_castSucc_succ_eq (n := n + 1)
        (⟨qi.val, by omega⟩ : Fin (n + 1)) y, hy]
      rfl
    set zL : barObj C R L (n + 1) :=
      ⟨(nerve C).δ ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ) F,
        transportL hLInnerLeft l, transportR hLInnerRight r⟩ with hzLdef
    set zR : barObj C R L (n + 1) :=
      ⟨(nerve C).δ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ) F,
        transportL hRInnerLeft l, transportR hRInnerRight r⟩ with hzRdef
    have hzL : barδ ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ) y = zL := by
      rw [hzLdef]
      exact hInnerL
    have hzR : barδ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ) y = zR := by
      rw [hzRdef]
      exact hInnerR
    rw [hzL, hzR]
    have hLOuterLeft :=
      leftδ_of_val_ne_zero (n := n) (i := qi.castSucc.succ)
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega)
        ((nerve C).δ ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ) F)
    have hLOuterRight :=
      rightδ_of_val_ne_last (n := n) (i := qi.castSucc.succ)
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega)
        ((nerve C).δ ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ) F)
    have hROuterLeft :=
      leftδ_of_val_ne_zero (n := n) (i := qj.castSucc.succ)
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega)
        ((nerve C).δ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ) F)
    have hROuterRight :=
      rightδ_of_val_ne_last (n := n) (i := qj.castSucc.succ)
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega)
        ((nerve C).δ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ) F)
    have hOuterL : barδ (qi.castSucc.succ) zL =
        ⟨(nerve C).δ (qi.castSucc.succ)
          ((nerve C).δ ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ) F),
          transportL hLOuterLeft (transportL hLInnerLeft l),
          transportR hLOuterRight (transportR hLInnerRight r)⟩ := by
      rw [barδ_castSucc_succ_eq (n := n) qi zL, hzLdef]
      rfl
    have hOuterR : barδ (qj.castSucc.succ) zR =
        ⟨(nerve C).δ (qj.castSucc.succ)
          ((nerve C).δ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ) F),
          transportL hROuterLeft (transportL hRInnerLeft l),
          transportR hROuterRight (transportR hRInnerRight r)⟩ := by
      rw [barδ_castSucc_succ_eq (n := n) qj zR, hzRdef]
      rfl
    have hFinalL :
        ((nerve C).δ (qi.castSucc.succ)
            ((nerve C).δ ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ) F)).left =
          ((nerve C).δ (qj.castSucc.succ)
            ((nerve C).δ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ) F)).left :=
      congrArg (fun G => G.left) hChain
    have hFinalR :
        ((nerve C).δ (qi.castSucc.succ)
            ((nerve C).δ ((⟨qj.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ) F)).right =
          ((nerve C).δ (qj.castSucc.succ)
            ((nerve C).δ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ) F)).right :=
      congrArg (fun G => G.right) hChain
    have hPairAux :
        ∀ {X0 XL1 ZL1 XL2 ZL2 Y0 YR1 ZR1 YR2 ZR2 : C} (x : L.obj X0) (y : R.obj (op Y0))
          (e1 : X0 = XL1) (e2 : XL1 = ZL1) (e3 : X0 = XL2) (e4 : XL2 = ZL2)
          (hT : ZL1 = ZL2)
        (er1 : Y0 = YR1) (er2 : YR1 = ZR1) (er3 : Y0 = YR2) (er4 : YR2 = ZR2)
          (hTR : ZR1 = ZR2),
        (transportL e2 (transportL e1 x), transportR er2 (transportR er1 y)) =
        cast (by cases hT; cases hTR; rfl)
          (transportL e4 (transportL e3 x),
            transportR er4 (transportR er3 y)) := by
      intro X0 XL1 ZL1 XL2 ZL2 Y0 YR1 ZR1 YR2 ZR2 x y e1 e2 e3 e4 hT er1 er2 er3 er4 hTR
      cases e1
      cases e3
      cases e2
      cases hT
      cases e4
      cases er1
      cases er3
      cases er2
      cases hTR
      cases er4
      rfl
    have hEq :=
      hPairAux l r hLInnerLeft hLOuterLeft hRInnerLeft hROuterLeft hFinalL
        hLInnerRight hLOuterRight hRInnerRight hROuterRight hFinalR
    have hCoeffHEq :
        (transportL hLOuterLeft (transportL hLInnerLeft l),
          transportR hLOuterRight (transportR hLInnerRight r)) ≍
        (transportL hROuterLeft (transportL hRInnerLeft l),
          transportR hROuterRight (transportR hRInnerRight r)) :=
      hEq ▸ cast_heq _ _
    rw [hOuterL, hOuterR]
    exact Sigma.ext hChain hCoeffHEq
  · -- interior, last: right action commutes with transports.
    set y : barObj C R L (n + 2) := ⟨F, l, r⟩ with hy
    have hChain := nerve_δ_comp_δ (n := n) (i := qi.castSucc.succ)
      (j := Fin.last (n + 1)) h F
    have hJs : (Fin.last (n + 1)).succ = Fin.last (n + 2) := rfl
    have hIc : (qi.castSucc.succ).castSucc =
        (⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ := by
      apply Fin.ext
      simp [Fin.val_castSucc, Fin.val_succ]
    rw [hJs, hIc] at hChain ⊢
    have hLInnerLeft : F.left =
        ((nerve C).δ (Fin.last (n + 2)) F).left :=
      leftδ_of_val_ne_zero (n := n + 1)
        (i := Fin.last (n + 2))
        (by rw [Fin.val_last]; omega) F
    have hLInnerRight : F.obj' (n + 1) =
        ((nerve C).δ (Fin.last (n + 2)) F).right :=
      (rightδ_last_eq (n := n + 1) F).symm
    have hRInnerLeft : F.left =
        ((nerve C).δ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ) F).left :=
      leftδ_of_val_ne_zero (n := n + 1)
        (i := ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ))
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega) F
    have hRInnerRight : F.right =
        ((nerve C).δ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ) F).right :=
      rightδ_of_val_ne_last (n := n + 1)
        (i := ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ))
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega) F
    have hInnerL : barδ (Fin.last (n + 2)) y =
        ⟨(nerve C).δ (Fin.last (n + 2)) F,
          transportL hLInnerLeft l,
          transportR hLInnerRight (R.map (Quiver.Hom.op (F.map' (n + 1) (n + 2))) r)⟩ := by
      rw [barδ_last_eq (n := n + 1) y, hy]
      rfl
    have hInnerR : barδ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ) y =
        ⟨(nerve C).δ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ) F,
          transportL hRInnerLeft l, transportR hRInnerRight r⟩ := by
      rw [barδ_castSucc_succ_eq (n := n + 1)
        (⟨qi.val, by omega⟩ : Fin (n + 1)) y, hy]
      rfl
    set zL : barObj C R L (n + 1) :=
      ⟨(nerve C).δ (Fin.last (n + 2)) F,
        transportL hLInnerLeft l,
        transportR hLInnerRight (R.map (Quiver.Hom.op (F.map' (n + 1) (n + 2))) r)⟩ with hzLdef
    set zR : barObj C R L (n + 1) :=
      ⟨(nerve C).δ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ) F,
        transportL hRInnerLeft l, transportR hRInnerRight r⟩ with hzRdef
    have hzL : barδ (Fin.last (n + 2)) y = zL := by
      rw [hzLdef]
      exact hInnerL
    have hzR : barδ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ) y = zR := by
      rw [hzRdef]
      exact hInnerR
    rw [hzL, hzR]
    have hLOuterLeft :=
      leftδ_of_val_ne_zero (n := n) (i := qi.castSucc.succ)
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega)
        ((nerve C).δ (Fin.last (n + 2)) F)
    have hLOuterRight :=
      rightδ_of_val_ne_last (n := n) (i := qi.castSucc.succ)
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega)
        ((nerve C).δ (Fin.last (n + 2)) F)
    have hROuterLeft :=
      leftδ_of_val_ne_zero (n := n) (i := Fin.last (n + 1))
        (by rw [Fin.val_last]; omega)
        ((nerve C).δ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ) F)
    have hROuterRight :=
      (rightδ_last_eq (n := n)
        ((nerve C).δ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ) F)).symm
    have hOuterL : barδ (qi.castSucc.succ) zL =
        ⟨(nerve C).δ (qi.castSucc.succ) ((nerve C).δ (Fin.last (n + 2)) F),
          transportL hLOuterLeft (transportL hLInnerLeft l),
          transportR hLOuterRight
            (transportR hLInnerRight (R.map (Quiver.Hom.op (F.map' (n + 1) (n + 2))) r))⟩ := by
      rw [barδ_castSucc_succ_eq (n := n) qi zL, hzLdef]
      rfl
    have hOuterR : barδ (Fin.last (n + 1)) zR =
        ⟨(nerve C).δ (Fin.last (n + 1))
          ((nerve C).δ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ) F),
          transportL hROuterLeft (transportL hRInnerLeft l),
          transportR hROuterRight
            (R.map (Quiver.Hom.op
              (((nerve C).δ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ) F).map' n (n + 1)))
              (transportR hRInnerRight r))⟩ := by
      rw [barδ_last_eq (n := n) zR, hzRdef]
      rfl
    have hFinalL : ((nerve C).δ (qi.castSucc.succ) ((nerve C).δ (Fin.last (n + 2)) F)).left =
        ((nerve C).δ (Fin.last (n + 1))
          ((nerve C).δ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ) F)).left :=
      congrArg (fun G => G.left) hChain
    have hFinalR : ((nerve C).δ (qi.castSucc.succ) ((nerve C).δ (Fin.last (n + 2)) F)).right =
        ((nerve C).δ (Fin.last (n + 1))
          ((nerve C).δ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ) F)).right :=
      congrArg (fun G => G.right) hChain
    have hPostN :
        ((((nerve C).δ ((⟨qi.val, Nat.lt_succ_of_lt qi.isLt⟩ : Fin (n + 1)).castSucc.succ) F).obj' n
              (Nat.le_succ n))) = F.obj' (n + 1) (Nat.le_succ (n + 1)) :=
      postFace_secondLast_obj (n := n) F qi _ rfl
    have hBridge :
        ((((nerve C).δ ((⟨qi.val, Nat.lt_succ_of_lt qi.isLt⟩ : Fin (n + 1)).castSucc.succ) F).map' n
              (n + 1)) ≫ eqToHom hRInnerRight.symm) =
          (eqToHom hPostN ≫ F.map' (n + 1) (n + 2)) := by
      have hpkN :
          ((((⟨qi.val, Nat.lt_succ_of_lt qi.isLt⟩ : Fin (n + 1)).castSucc.succ)) :
              Fin (n + 3)) ≤
            ((⟨n, by omega⟩ : Fin (n + 2)).castSucc) := by
        change qi.val + 1 ≤ n
        omega
      have hSuccN :
          ((((⟨qi.val, Nat.lt_succ_of_lt qi.isLt⟩ : Fin (n + 1)).castSucc.succ)) :
              Fin (n + 3)).succAbove ((⟨n, by omega⟩ : Fin (n + 2))) =
            ((⟨n + 1, by omega⟩ : Fin (n + 3))) := by
        have h := Fin.succAbove_of_le_castSucc _ _ hpkN
        simpa using h
      have hpkLast :
          ((((⟨qi.val, Nat.lt_succ_of_lt qi.isLt⟩ : Fin (n + 1)).castSucc.succ)) :
              Fin (n + 3)) ≤
            ((⟨n + 1, by omega⟩ : Fin (n + 2)).castSucc) := by
        change qi.val + 1 ≤ n + 1
        omega
      have hSuccLast :
          ((((⟨qi.val, Nat.lt_succ_of_lt qi.isLt⟩ : Fin (n + 1)).castSucc.succ)) :
              Fin (n + 3)).succAbove ((⟨n + 1, by omega⟩ : Fin (n + 2))) =
            ((⟨n + 2, by omega⟩ : Fin (n + 3))) := by
        have h := Fin.succAbove_of_le_castSucc _ _ hpkLast
        simpa using h
      dsimp only [ComposableArrows.map', CategoryTheory.nerve.δ_obj, hSuccN, hSuccLast] at ⊢
      change ((F.whiskerLeft
              ((SimplexCategory.toCat.map
                  (SimplexCategory.δ
                    (((⟨qi.val,
                          Nat.lt_succ_of_lt qi.isLt⟩ :
                            Fin (n + 1)).castSucc.succ))).op.unop).toFunctor)).map
            (homOfLE _) ≫ eqToHom hRInnerRight.symm) =
          (eqToHom hPostN ≫ F.map' (n + 1) (n + 2)) at ⊢
      dsimp only [ComposableArrows.whiskerLeft, ComposableArrows.map'] at ⊢
      have h0 : ((⟨n, by omega⟩ : Fin (n + 2))) ⟶ ((⟨n + 1, by omega⟩ : Fin (n + 2))) :=
        homOfLE (by simp only [Fin.mk_le_mk]; omega)
      have hMid : ((⟨n + 1, by omega⟩ : Fin (n + 3))) ⟶ ((⟨n + 2, by omega⟩ : Fin (n + 3))) :=
        homOfLE (by simp only [Fin.mk_le_mk]; omega)
      have hΦobjN :
          (((SimplexCategory.toCat.map
              (SimplexCategory.δ
                (((⟨qi.val,
                      Nat.lt_succ_of_lt qi.isLt⟩ :
                        Fin (n + 1)).castSucc.succ))).op.unop).toFunctor).obj
              (⟨n, by omega⟩ : Fin (n + 2))) =
            ((⟨n + 1, by omega⟩ : Fin (n + 3))) := hSuccN
      have hΦobjLast :
          (((SimplexCategory.toCat.map
              (SimplexCategory.δ
                (((⟨qi.val,
                      Nat.lt_succ_of_lt qi.isLt⟩ :
                        Fin (n + 1)).castSucc.succ))).op.unop).toFunctor).obj
              (⟨n + 1, by omega⟩ : Fin (n + 2))) =
            ((⟨n + 2, by omega⟩ : Fin (n + 3))) := hSuccLast
      have hChain2 :
          (((SimplexCategory.toCat.map
              (SimplexCategory.δ
                (((⟨qi.val,
                      Nat.lt_succ_of_lt qi.isLt⟩ :
                        Fin (n + 1)).castSucc.succ))).op.unop).toFunctor).map
              h0) =
            (eqToHom hΦobjN ≫ hMid ≫ eqToHom hΦobjLast.symm) := rfl
      have hFmap2 :
          F.map
              (((SimplexCategory.toCat.map
                  (SimplexCategory.δ
                    (((⟨qi.val,
                          Nat.lt_succ_of_lt qi.isLt⟩ :
                            Fin (n + 1)).castSucc.succ))).op.unop).toFunctor).map
                h0) =
            (eqToHom (congrArg F.obj hΦobjN) ≫ F.map hMid) ≫
              F.map (eqToHom hΦobjLast.symm) :=
        calc F.map
              (((SimplexCategory.toCat.map
                  (SimplexCategory.δ
                    (((⟨qi.val,
                          Nat.lt_succ_of_lt qi.isLt⟩ :
                            Fin (n + 1)).castSucc.succ))).op.unop).toFunctor).map
                h0)
            = F.map (eqToHom hΦobjN ≫ hMid ≫ eqToHom hΦobjLast.symm) := congrArg F.map hChain2
          _ = F.map (eqToHom hΦobjN ≫ hMid) ≫ F.map (eqToHom hΦobjLast.symm) :=
            Functor.map_comp F (eqToHom hΦobjN ≫ hMid) (eqToHom hΦobjLast.symm)
          _ = (F.map (eqToHom hΦobjN) ≫ F.map hMid) ≫ F.map (eqToHom hΦobjLast.symm) :=
            congrArg (· ≫ F.map (eqToHom hΦobjLast.symm)) (Functor.map_comp F (eqToHom hΦobjN) hMid)
          _ = (eqToHom (congrArg F.obj hΦobjN) ≫ F.map hMid) ≫ F.map (eqToHom hΦobjLast.symm) :=
            congrArg (· ≫ F.map (eqToHom hΦobjLast.symm))
              (congrArg (· ≫ F.map hMid) (eqToHom_map F hΦobjN))
      have hMidEq : F.map hMid = F.map' (n + 1) (n + 2) := by
        simp only [← homOfLE_leOfHom hMid, ComposableArrows.map']
      change (F.map
              (((SimplexCategory.toCat.map
                  (SimplexCategory.δ
                    (((⟨qi.val,
                          Nat.lt_succ_of_lt qi.isLt⟩ :
                            Fin (n + 1)).castSucc.succ))).op.unop).toFunctor).map
                h0) ≫ eqToHom hRInnerRight.symm) =
          (eqToHom hPostN ≫ F.map' (n + 1) (n + 2)) at ⊢
      rw [hFmap2, hMidEq] at ⊢
      have h10 : (F.map (eqToHom hΦobjLast.symm) ≫ eqToHom hRInnerRight.symm) = 𝟙 _ :=
        (congrArg (· ≫ eqToHom hRInnerRight.symm) (eqToHom_map F hΦobjLast.symm)).trans
          ((eqToHom_trans _ _).trans (eqToHom_refl _ _))
      have hEqP : congrArg F.obj hΦobjN = hPostN := rfl
      have hEE : eqToHom (congrArg F.obj hΦobjN) = eqToHom hPostN := congrArg eqToHom hEqP
      simp only [Category.assoc] at ⊢
      rw [h10, Category.comp_id, hEE] at ⊢
      rfl
    have hPairAux :
        ∀ {X0 XL1 ZL1 XL2 ZL2 Y0 YM_L YR1 ZR1 YR2 YM_R ZR2 : C} (x : L.obj X0)
          (y : R.obj (op Y0))
      (e1 : X0 = XL1) (e2 : XL1 = ZL1) (e3 : X0 = XL2) (e4 : XL2 = ZL2) (hT : ZL1 = ZL2)
      (gL : YM_L ⟶ Y0) (gR : YM_R ⟶ YR2)
      (er1 : YM_L = YR1) (er2 : YR1 = ZR1) (er3 : Y0 = YR2) (er4 : YM_R = ZR2) (hTR : ZR1 = ZR2)
      (eMid : YM_R = YM_L)
      (hMap : gR ≫ eqToHom er3.symm = eqToHom eMid ≫ gL),
      (transportL e2 (transportL e1 x), transportR er2 (transportR er1 (R.map gL.op y))) =
      cast (by cases hT; cases hTR; rfl)
        (transportL e4 (transportL e3 x),
          transportR er4 (R.map gR.op (transportR er3 y))) := by
      intro X0 XL1 ZL1 XL2 ZL2 Y0 YM_L YR1 ZR1 YR2 YM_R ZR2 x y e1 e2 e3 e4 hT gL gR
        er1 er2 er3 er4 hTR eMid hMap
      cases e1
      cases e3
      cases e2
      cases hT
      cases e4
      cases er3
      cases er1
      cases er2
      cases hTR
      cases er4
      cases eMid
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hMap
      subst hMap
      rfl
    have hEq :=
      hPairAux l r hLInnerLeft hLOuterLeft hRInnerLeft hROuterLeft hFinalL
        (F.map' (n + 1) (n + 2))
        (((nerve C).δ
            ((⟨qi.val,
                  Nat.lt_succ_of_lt qi.isLt⟩ : Fin (n + 1)).castSucc.succ) F).map' n
            (n + 1))
        hLInnerRight hLOuterRight hRInnerRight hROuterRight hFinalR hPostN hBridge
    have hCoeffHEq :
        (transportL hLOuterLeft (transportL hLInnerLeft l),
          transportR hLOuterRight
            (transportR hLInnerRight (R.map (Quiver.Hom.op (F.map' (n + 1) (n + 2))) r))) ≍
        (transportL hROuterLeft (transportL hRInnerLeft l),
          transportR hROuterRight
            (R.map (Quiver.Hom.op
              (((nerve C).δ
                  ((⟨qi.val,
                        Nat.lt_succ_of_lt qi.isLt⟩ : Fin (n + 1)).castSucc.succ) F).map' n
                (n + 1)))
              (transportR hRInnerRight r))) :=
      hEq ▸ cast_heq _ _
    rw [hOuterL, hOuterR]
    exact Sigma.ext hChain hCoeffHEq
  · -- last, 0 impossible.
    have hval : (Fin.last (n + 1) : Fin (n + 2)).val ≤ (0 : Fin (n + 2)).val := h
    rw [Fin.val_last, Fin.val_zero] at hval
    omega
  · -- last, interior impossible.
    have hval : (Fin.last (n + 1) : Fin (n + 2)).val ≤ (qj.castSucc.succ : Fin (n + 2)).val := h
    rw [Fin.val_last, Fin.val_succ, Fin.val_castSucc] at hval
    have hqj := qj.isLt
    omega
  · -- last, last: two right actions cohere via `R.map_comp`.
    set y : barObj C R L (n + 2) := ⟨F, l, r⟩ with hy
    have hChain := nerve_δ_comp_δ (n := n) (i := Fin.last (n + 1)) (j := Fin.last (n + 1))
      (by omega) F
    have hJs : (Fin.last (n + 1)).succ = Fin.last (n + 2) := rfl
    have hIc : (Fin.last (n + 1)).castSucc =
        (⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ := by
      apply Fin.ext
      simp [Fin.val_castSucc, Fin.val_last]
    have hCompR : F.map' n (n + 2) = F.map' n (n + 1) ≫ F.map' (n + 1) (n + 2) :=
      ComposableArrows.map'_comp F n (n + 1) (n + 2)
    rw [hJs, hIc] at hChain ⊢
    have hLInnerLeft : F.left =
        ((nerve C).δ (Fin.last (n + 2)) F).left :=
      leftδ_of_val_ne_zero (n := n + 1)
        (i := Fin.last (n + 2))
        (by rw [Fin.val_last]; omega) F
    have hLInnerRight : F.obj' (n + 1) =
        ((nerve C).δ (Fin.last (n + 2)) F).right :=
      (rightδ_last_eq (n := n + 1) F).symm
    have hRInnerLeft : F.left =
        ((nerve C).δ ((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ) F).left :=
      leftδ_of_val_ne_zero (n := n + 1)
        (i := ((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ))
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega) F
    have hRInnerRight : F.right =
        ((nerve C).δ ((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ) F).right :=
      rightδ_of_val_ne_last (n := n + 1)
        (i := ((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ))
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega) F
    have hInnerL : barδ (Fin.last (n + 2)) y =
        ⟨(nerve C).δ (Fin.last (n + 2)) F,
          transportL hLInnerLeft l,
          transportR hLInnerRight (R.map (Quiver.Hom.op (F.map' (n + 1) (n + 2))) r)⟩ := by
      rw [barδ_last_eq (n := n + 1) y, hy]
      rfl
    have hInnerR : barδ ((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ) y =
        ⟨(nerve C).δ ((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ) F,
          transportL hRInnerLeft l, transportR hRInnerRight r⟩ := by
      rw [barδ_castSucc_succ_eq (n := n + 1)
        (⟨n, by omega⟩ : Fin (n + 1)) y, hy]
      rfl
    set zL : barObj C R L (n + 1) :=
      ⟨(nerve C).δ (Fin.last (n + 2)) F,
        transportL hLInnerLeft l,
        transportR hLInnerRight (R.map (Quiver.Hom.op (F.map' (n + 1) (n + 2))) r)⟩ with hzLdef
    set zR : barObj C R L (n + 1) :=
      ⟨(nerve C).δ ((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ) F,
        transportL hRInnerLeft l, transportR hRInnerRight r⟩ with hzRdef
    have hzL : barδ (Fin.last (n + 2)) y = zL := by
      rw [hzLdef]
      exact hInnerL
    have hzR : barδ ((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ) y = zR := by
      rw [hzRdef]
      exact hInnerR
    rw [hzL, hzR]
    have hLOuterLeft :=
      leftδ_of_val_ne_zero (n := n) (i := Fin.last (n + 1))
        (by rw [Fin.val_last]; omega)
        ((nerve C).δ (Fin.last (n + 2)) F)
    have hLOuterRight :=
      (rightδ_last_eq (n := n) ((nerve C).δ (Fin.last (n + 2)) F)).symm
    have hROuterLeft :=
      leftδ_of_val_ne_zero (n := n) (i := Fin.last (n + 1))
        (by rw [Fin.val_last]; omega)
        ((nerve C).δ ((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ) F)
    have hROuterRight :=
      (rightδ_last_eq (n := n)
        ((nerve C).δ ((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ) F)).symm
    have hOuterL : barδ (Fin.last (n + 1)) zL =
        ⟨(nerve C).δ (Fin.last (n + 1)) ((nerve C).δ (Fin.last (n + 2)) F),
          transportL hLOuterLeft (transportL hLInnerLeft l),
          transportR hLOuterRight
            (R.map (Quiver.Hom.op
              (((nerve C).δ (Fin.last (n + 2)) F).map' n (n + 1)))
              (transportR hLInnerRight (R.map (Quiver.Hom.op (F.map' (n + 1) (n + 2))) r)))⟩ := by
      rw [barδ_last_eq (n := n) zL, hzLdef]
      rfl
    have hOuterR : barδ (Fin.last (n + 1)) zR =
        ⟨(nerve C).δ (Fin.last (n + 1))
          ((nerve C).δ ((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ) F),
          transportL hROuterLeft (transportL hRInnerLeft l),
          transportR hROuterRight
            (R.map (Quiver.Hom.op
              (((nerve C).δ ((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ) F).map' n (n + 1)))
              (transportR hRInnerRight r))⟩ := by
      rw [barδ_last_eq (n := n) zR, hzRdef]
      rfl
    have hFinalL : ((nerve C).δ (Fin.last (n + 1)) ((nerve C).δ (Fin.last (n + 2)) F)).left =
        ((nerve C).δ (Fin.last (n + 1))
          ((nerve C).δ ((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ) F)).left :=
      congrArg (fun G => G.left) hChain
    have hFinalR : ((nerve C).δ (Fin.last (n + 1)) ((nerve C).δ (Fin.last (n + 2)) F)).right =
        ((nerve C).δ (Fin.last (n + 1))
          ((nerve C).δ ((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ) F)).right :=
      congrArg (fun G => G.right) hChain
    have hPairAuxLL : ∀ {X0 XL1 ZL1 XL2 ZL2 Y0 YM1 YR1 ZR1 YR2 YM2L YM2R ZR2 : C}
        (x : L.obj X0) (y : R.obj (op Y0))
        (e1 : X0 = XL1) (e2 : XL1 = ZL1) (e3 : X0 = XL2) (e4 : XL2 = ZL2)
        (hT : ZL1 = ZL2)
        (gInner : YM1 ⟶ Y0) (gOuterL : YM2L ⟶ YR1) (gOuterR : YM2R ⟶ YR2)
        (er1 : YM1 = YR1) (er2 : YM2L = ZR1) (er3 : Y0 = YR2) (er4 : YM2R = ZR2)
        (hTR : ZR1 = ZR2)
        (hMapR : gOuterR ≫ eqToHom er3.symm =
          eqToHom er4 ≫ eqToHom hTR.symm ≫ eqToHom er2.symm ≫
            (gOuterL ≫ eqToHom er1.symm ≫ gInner)),
        (transportL e2 (transportL e1 x),
          transportR er2 (R.map gOuterL.op (transportR er1 (R.map gInner.op y)))) =
        cast (by cases hT; cases hTR; rfl)
          (transportL e4 (transportL e3 x),
            transportR er4 (R.map gOuterR.op (transportR er3 y))) := by
      intro X0 XL1 ZL1 XL2 ZL2 Y0 YM1 YR1 ZR1 YR2 YM2L YM2R ZR2 x y e1 e2 e3 e4 hT
        gInner gOuterL gOuterR er1 er2 er3 er4 hTR hMapR
      cases e1
      cases e3
      cases e2
      cases hT
      cases e4
      cases er3
      cases er1
      cases er2
      cases hTR
      cases er4
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hMapR
      subst hMapR
      simp only [op_comp, R.map_comp]
      rfl
    have hMapR : (((nerve C).δ ((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ) F).map' n (n + 1)) ≫
          eqToHom hRInnerRight.symm =
        eqToHom hROuterRight ≫ eqToHom hFinalR.symm ≫ eqToHom hLOuterRight.symm ≫
          ((((nerve C).δ (Fin.last (n + 2)) F).map' n (n + 1)) ≫
            eqToHom hLInnerRight.symm ≫ F.map' (n + 1) (n + 2)) := by
      have hpkR : ((((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ)) : Fin (n + 3)) ≤
          ((⟨n + 1, by omega⟩ : Fin (n + 2)).castSucc) := by
        change n + 1 ≤ n + 1
        omega
      have hSuccR : ((((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ)) : Fin (n + 3)).succAbove
          ((⟨n + 1, by omega⟩ : Fin (n + 2))) = ((⟨n + 2, by omega⟩ : Fin (n + 3))) := by
        have h := Fin.succAbove_of_le_castSucc _ _ hpkR
        simpa using h
      have hSuccR_N : ((((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ)) : Fin (n + 3)).succAbove
          ((⟨n, by omega⟩ : Fin (n + 2))) = ((⟨n, by omega⟩ : Fin (n + 3))) := by
        have hq : ((((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ)) : Fin (n + 3)) =
            (((⟨n + 1, by omega⟩ : Fin (n + 2)).castSucc) : Fin (n + 3)) := by
          apply Fin.ext
          simp
        have hlt : (⟨n, by omega⟩ : Fin (n + 2)) < (⟨n + 1, by omega⟩ : Fin (n + 2)) := by
          simp
        have h := Fin.succAbove_castSucc_of_lt _ _ hlt
        rw [hq] at ⊢
        rw [h]
        apply Fin.ext
        simp
      have hSuccL_N : (Fin.last (n + 2) : Fin (n + 3)).succAbove
          ((⟨n, by omega⟩ : Fin (n + 2))) = ((⟨n, by omega⟩ : Fin (n + 3))) := by
        apply Fin.ext
        simp
      have hSuccL_Last : (Fin.last (n + 2) : Fin (n + 3)).succAbove
          ((⟨n + 1, by omega⟩ : Fin (n + 2))) = ((⟨n + 1, by omega⟩ : Fin (n + 3))) := by
        apply Fin.ext
        simp
      dsimp only [ComposableArrows.map', CategoryTheory.nerve.δ_obj, hSuccR, hSuccR_N,
        hSuccL_N, hSuccL_Last] at ⊢
      change ((F.whiskerLeft ((SimplexCategory.toCat.map (SimplexCategory.δ
        (((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ))).op.unop).toFunctor)).map (homOfLE _) ≫
        eqToHom hRInnerRight.symm) =
        eqToHom hROuterRight ≫ eqToHom hFinalR.symm ≫ eqToHom hLOuterRight.symm ≫
          (((F.whiskerLeft ((SimplexCategory.toCat.map (SimplexCategory.δ
            (Fin.last (n + 2))).op.unop).toFunctor)).map (homOfLE _) ≫
            eqToHom hLInnerRight.symm ≫ F.map' (n + 1) (n + 2))) at ⊢
      dsimp only [ComposableArrows.whiskerLeft, ComposableArrows.map'] at ⊢
      have h0R : ((⟨n, by omega⟩ : Fin (n + 2))) ⟶ ((⟨n + 1, by omega⟩ : Fin (n + 2))) :=
        homOfLE (by simp only [Fin.mk_le_mk]; omega)
      have hMidR : ((⟨n, by omega⟩ : Fin (n + 3))) ⟶ ((⟨n + 2, by omega⟩ : Fin (n + 3))) :=
        homOfLE (by simp only [Fin.mk_le_mk]; omega)
      have h0L : ((⟨n, by omega⟩ : Fin (n + 2))) ⟶ ((⟨n + 1, by omega⟩ : Fin (n + 2))) :=
        homOfLE (by simp only [Fin.mk_le_mk]; omega)
      have hPhiR_N : (((SimplexCategory.toCat.map (SimplexCategory.δ
          (((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ))).op.unop).toFunctor).obj
          (⟨n, by omega⟩ : Fin (n + 2))) = ((⟨n, by omega⟩ : Fin (n + 3))) := hSuccR_N
      have hPhiR_Last : (((SimplexCategory.toCat.map (SimplexCategory.δ
          (((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ))).op.unop).toFunctor).obj
          (⟨n + 1, by omega⟩ : Fin (n + 2))) = ((⟨n + 2, by omega⟩ : Fin (n + 3))) := hSuccR
      have hPhiL_N : (((SimplexCategory.toCat.map (SimplexCategory.δ
          (Fin.last (n + 2))).op.unop).toFunctor).obj
          (⟨n, by omega⟩ : Fin (n + 2))) = ((⟨n, by omega⟩ : Fin (n + 3))) := hSuccL_N
      have hPhiL_Last : (((SimplexCategory.toCat.map (SimplexCategory.δ
          (Fin.last (n + 2))).op.unop).toFunctor).obj
          (⟨n + 1, by omega⟩ : Fin (n + 2))) = ((⟨n + 1, by omega⟩ : Fin (n + 3))) := hSuccL_Last
      have hChainR : (((SimplexCategory.toCat.map (SimplexCategory.δ
          (((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ))).op.unop).toFunctor).map h0R) =
          (eqToHom hPhiR_N ≫ hMidR ≫ eqToHom hPhiR_Last.symm) := rfl
      have hMidL : ((⟨n, by omega⟩ : Fin (n + 3))) ⟶ ((⟨n + 1, by omega⟩ : Fin (n + 3))) :=
        homOfLE (by simp only [Fin.mk_le_mk]; omega)
      have hChainL : (((SimplexCategory.toCat.map (SimplexCategory.δ
          (Fin.last (n + 2))).op.unop).toFunctor).map h0L) =
          (eqToHom hPhiL_N ≫ hMidL ≫ eqToHom hPhiL_Last.symm) := rfl
      have hFmapR : F.map (((SimplexCategory.toCat.map (SimplexCategory.δ
          (((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ))).op.unop).toFunctor).map h0R) =
          (eqToHom (congrArg F.obj hPhiR_N) ≫ F.map hMidR) ≫
            F.map (eqToHom hPhiR_Last.symm) :=
        calc F.map (((SimplexCategory.toCat.map (SimplexCategory.δ
            (((⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)).castSucc.succ))).op.unop).toFunctor).map h0R)
            = F.map (eqToHom hPhiR_N ≫ hMidR ≫ eqToHom hPhiR_Last.symm) :=
              congrArg F.map hChainR
          _ = F.map (eqToHom hPhiR_N ≫ hMidR) ≫ F.map (eqToHom hPhiR_Last.symm) :=
            Functor.map_comp F (eqToHom hPhiR_N ≫ hMidR) (eqToHom hPhiR_Last.symm)
          _ = (F.map (eqToHom hPhiR_N) ≫ F.map hMidR) ≫ F.map (eqToHom hPhiR_Last.symm) :=
            congrArg (· ≫ F.map (eqToHom hPhiR_Last.symm))
              (Functor.map_comp F (eqToHom hPhiR_N) hMidR)
          _ = (eqToHom (congrArg F.obj hPhiR_N) ≫ F.map hMidR) ≫
              F.map (eqToHom hPhiR_Last.symm) :=
            congrArg (· ≫ F.map (eqToHom hPhiR_Last.symm))
              (congrArg (· ≫ F.map hMidR) (eqToHom_map F hPhiR_N))
      have hFmapL : F.map (((SimplexCategory.toCat.map (SimplexCategory.δ
          (Fin.last (n + 2))).op.unop).toFunctor).map h0L) =
          (eqToHom (congrArg F.obj hPhiL_N) ≫ F.map hMidL) ≫
            F.map (eqToHom hPhiL_Last.symm) :=
        calc F.map (((SimplexCategory.toCat.map (SimplexCategory.δ
            (Fin.last (n + 2))).op.unop).toFunctor).map h0L)
            = F.map (eqToHom hPhiL_N ≫ hMidL ≫ eqToHom hPhiL_Last.symm) :=
              congrArg F.map hChainL
          _ = F.map (eqToHom hPhiL_N ≫ hMidL) ≫ F.map (eqToHom hPhiL_Last.symm) :=
            Functor.map_comp F (eqToHom hPhiL_N ≫ hMidL) (eqToHom hPhiL_Last.symm)
          _ = (F.map (eqToHom hPhiL_N) ≫ F.map hMidL) ≫
              F.map (eqToHom hPhiL_Last.symm) :=
            congrArg (· ≫ F.map (eqToHom hPhiL_Last.symm))
              (Functor.map_comp F (eqToHom hPhiL_N) hMidL)
          _ = (eqToHom (congrArg F.obj hPhiL_N) ≫ F.map hMidL) ≫
              F.map (eqToHom hPhiL_Last.symm) :=
            congrArg (· ≫ F.map (eqToHom hPhiL_Last.symm))
              (congrArg (· ≫ F.map hMidL) (eqToHom_map F hPhiL_N))
      have hMidEqR : F.map hMidR = F.map' n (n + 2) := by
        simp only [← homOfLE_leOfHom hMidR, ComposableArrows.map']
      have hMidEqL : F.map hMidL = F.map' n (n + 1) := by
        simp only [← homOfLE_leOfHom hMidL, ComposableArrows.map']
      change (F.map (((SimplexCategory.toCat.map (SimplexCategory.δ
          (((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ))).op.unop).toFunctor).map h0R) ≫
          eqToHom hRInnerRight.symm) =
        (eqToHom hROuterRight ≫ eqToHom hFinalR.symm ≫ eqToHom hLOuterRight.symm ≫
          (F.map (((SimplexCategory.toCat.map (SimplexCategory.δ
            (Fin.last (n + 2))).op.unop).toFunctor).map h0L) ≫
            eqToHom hLInnerRight.symm ≫ F.map' (n + 1) (n + 2))) at ⊢
      rw [hFmapR, hFmapL, hMidEqR, hMidEqL, hCompR] at ⊢
      simp only [Category.assoc] at ⊢
      have hCancelR : (F.map (eqToHom hPhiR_Last.symm) ≫ eqToHom hRInnerRight.symm) = 𝟙 _ :=
        (congrArg (· ≫ eqToHom hRInnerRight.symm) (eqToHom_map F hPhiR_Last.symm)).trans
          ((eqToHom_trans _ _).trans (eqToHom_refl _ _))
      rw [hCancelR]
      simp only [Category.comp_id] at ⊢
      have hEqN : congrArg F.obj hPhiR_N = congrArg F.obj hSuccR_N := rfl
      rw [hEqN]
      have hCancelL : (F.map (eqToHom hPhiL_Last.symm) ≫ eqToHom hLInnerRight.symm) = 𝟙 _ :=
        (congrArg (· ≫ eqToHom hLInnerRight.symm) (eqToHom_map F hPhiL_Last.symm)).trans
          ((eqToHom_trans _ _).trans (eqToHom_refl _ _))
      have hSeg : ((eqToHom (congrArg F.obj hPhiL_N) ≫ (F.map' n (n + 1) ≫
          F.map (eqToHom hPhiL_Last.symm))) ≫ (eqToHom hLInnerRight.symm ≫
          F.map' (n + 1) (n + 2))) =
          ((eqToHom (congrArg F.obj hPhiL_N) ≫ F.map' n (n + 1)) ≫
          F.map' (n + 1) (n + 2)) :=
        (Category.assoc (eqToHom (congrArg F.obj hPhiL_N))
          (F.map' n (n + 1) ≫ F.map (eqToHom hPhiL_Last.symm))
          (eqToHom hLInnerRight.symm ≫ F.map' (n + 1) (n + 2))).trans
        ((congrArg (eqToHom (congrArg F.obj hPhiL_N) ≫ ·)
          (Category.assoc (F.map' n (n + 1)) (F.map (eqToHom hPhiL_Last.symm))
            (eqToHom hLInnerRight.symm ≫ F.map' (n + 1) (n + 2)))).trans
        ((congrArg (eqToHom (congrArg F.obj hPhiL_N) ≫ ·)
          (congrArg (F.map' n (n + 1) ≫ ·)
            (Category.assoc (F.map (eqToHom hPhiL_Last.symm))
              (eqToHom hLInnerRight.symm) (F.map' (n + 1) (n + 2))).symm)).trans
        ((congrArg (eqToHom (congrArg F.obj hPhiL_N) ≫ ·)
          (congrArg (F.map' n (n + 1) ≫ ·)
            (congrArg (· ≫ F.map' (n + 1) (n + 2)) hCancelL))).trans
        ((congrArg (eqToHom (congrArg F.obj hPhiL_N) ≫ ·)
          (congrArg (F.map' n (n + 1) ≫ ·)
            (Category.id_comp (F.map' (n + 1) (n + 2))))).trans
          (Category.assoc (eqToHom (congrArg F.obj hPhiL_N))
            (F.map' n (n + 1)) (F.map' (n + 1) (n + 2))).symm))))
      have hPre : ((eqToHom hROuterRight ≫ eqToHom hFinalR.symm) ≫
          eqToHom hLOuterRight.symm) ≫ eqToHom (congrArg F.obj hPhiL_N) =
          eqToHom (congrArg F.obj hSuccR_N) :=
        (congrArg (· ≫ eqToHom (congrArg F.obj hPhiL_N))
          (congrArg (· ≫ eqToHom hLOuterRight.symm)
            (eqToHom_trans hROuterRight hFinalR.symm))).trans
        ((congrArg (· ≫ eqToHom (congrArg F.obj hPhiL_N))
          (eqToHom_trans (hROuterRight.trans hFinalR.symm)
            hLOuterRight.symm)).trans
        ((eqToHom_trans ((hROuterRight.trans hFinalR.symm).trans hLOuterRight.symm)
          (congrArg F.obj hPhiL_N)).trans rfl))
      have c1 := congrArg (fun t => eqToHom hROuterRight ≫ (eqToHom hFinalR.symm ≫
        (eqToHom hLOuterRight.symm ≫ t))) hSeg
      have c2 : (eqToHom hROuterRight ≫ (eqToHom hFinalR.symm ≫ (eqToHom hLOuterRight.symm ≫
          ((eqToHom (congrArg F.obj hPhiL_N) ≫ F.map' n (n + 1)) ≫ F.map' (n + 1) (n + 2))))) =
          (((((eqToHom hROuterRight ≫ eqToHom hFinalR.symm) ≫ eqToHom hLOuterRight.symm) ≫
          eqToHom (congrArg F.obj hPhiL_N)) ≫ F.map' n (n + 1)) ≫ F.map' (n + 1) (n + 2)) := by
        simp only [← Category.assoc]
      have c3 := congrArg (fun p => (p ≫ F.map' n (n + 1)) ≫ F.map' (n + 1) (n + 2)) hPre
      have c4 : ((eqToHom (congrArg F.obj hSuccR_N) ≫ F.map' n (n + 1)) ≫
          F.map' (n + 1) (n + 2)) =
          (eqToHom (congrArg F.obj hSuccR_N) ≫ (F.map' n (n + 1) ≫
          F.map' (n + 1) (n + 2))) :=
        (Category.assoc (eqToHom (congrArg F.obj hSuccR_N))
          (F.map' n (n + 1)) (F.map' (n + 1) (n + 2))).trans rfl
      exact (c1.trans (c2.trans (c3.trans c4))).symm
    have hEq := hPairAuxLL l r hLInnerLeft hLOuterLeft hRInnerLeft hROuterLeft hFinalL
      (F.map' (n + 1) (n + 2)) (((nerve C).δ (Fin.last (n + 2)) F).map' n (n + 1))
      (((nerve C).δ ((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ) F).map' n (n + 1))
      hLInnerRight hLOuterRight hRInnerRight hROuterRight hFinalR hMapR
    have hCoeffHEq :
        (transportL hLOuterLeft (transportL hLInnerLeft l),
          transportR hLOuterRight
            (R.map (Quiver.Hom.op
              (((nerve C).δ (Fin.last (n + 2)) F).map' n (n + 1)))
              (transportR hLInnerRight (R.map (Quiver.Hom.op (F.map' (n + 1) (n + 2))) r)))) ≍
        (transportL hROuterLeft (transportL hRInnerLeft l),
          transportR hROuterRight
            (R.map (Quiver.Hom.op
              (((nerve C).δ ((⟨n, by omega⟩ : Fin (n + 1)).castSucc.succ) F).map' n (n + 1)))
              (transportR hRInnerRight r))) :=
      hEq ▸ cast_heq _ _
    rw [hOuterL, hOuterR]
    exact Sigma.ext hChain hCoeffHEq

/-- Face-degeneracy below: zero and interior live, last impossible. -/
theorem δ_comp_σ_of_le {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : i ≤ j.castSucc) (x : barObj C R L (n + 1)) :
    barδ (R := R) (L := L) i.castSucc (barσ j.succ x) =
      barσ (R := R) (L := L) j (barδ i x) := by
  obtain ⟨F, l, r⟩ := x
  have hi := fin_tri (n := n) i
  rcases hi with rfl | ⟨qi, rfl⟩ | rfl
  · have hChain := nerve_δ_comp_σ_of_le (n := n)
      (i := (0 : Fin (n + 2))) (j := j) h F
    have hIc : (0 : Fin (n + 2)).castSucc = (0 : Fin (n + 3)) := by
      apply Fin.ext
      simp
    set y : barObj C R L (n + 1) := ⟨F, l, r⟩ with hy
    have hInner : barδ (0 : Fin (n + 2)) y =
        ⟨(nerve C).δ (0 : Fin (n + 2)) F,
          transportL (leftδ_zero_eq (n := n) F).symm
            (L.map (F.map' 0 1 (Nat.zero_le 1) (Nat.succ_le_succ (Nat.zero_le _))) l),
          transportR (rightδ_of_val_ne_last (n := n) (i := (0 : Fin (n + 2))) (by simp) F) r⟩ := by
      rw [barδ_zero_eq (n := n) y, hy]
      rfl
    have hSigma : barσ (R := R) (L := L) j.succ y =
        ⟨(nerve C).σ j.succ F, transportL (leftσ_eq (n := n + 1) F) l,
          transportR (rightσ_eq (n := n + 1) F) r⟩ := by
      rw [hy]
      rfl
    rw [hIc, hSigma, hInner]
    set zS : barObj C R L (n + 2) :=
      ⟨(nerve C).σ j.succ F, transportL (leftσ_eq (n := n + 1) F) l,
        transportR (rightσ_eq (n := n + 1) F) r⟩ with hzSdef
    have hOuterL : barδ (0 : Fin ((n + 1) + 2)) zS =
        ⟨(nerve C).δ (0 : Fin ((n + 1) + 2)) ((nerve C).σ j.succ F),
          transportL (leftδ_zero_eq (n := n + 1) ((nerve C).σ j.succ F)).symm
            (L.map ((((nerve C).σ j.succ F).map' 0 1 (Nat.zero_le 1)
              (Nat.succ_le_succ (Nat.zero_le _))))
              (transportL (leftσ_eq (n := n + 1) F) l)),
          transportR
            (rightδ_of_val_ne_last (n := n + 1) (i := (0 : Fin ((n + 1) + 2)))
              (by simp) ((nerve C).σ j.succ F))
            (transportR (rightσ_eq (n := n + 1) F) r)⟩ := by
      rw [barδ_zero_eq (n := n + 1) zS, hzSdef]
      rfl
    have hOuterR : barσ (R := R) (L := L) j
        ⟨(nerve C).δ (0 : Fin (n + 2)) F,
          transportL (leftδ_zero_eq (n := n) F).symm
            (L.map (F.map' 0 1 (Nat.zero_le 1) (Nat.succ_le_succ (Nat.zero_le _))) l),
          transportR (rightδ_of_val_ne_last (n := n) (i := (0 : Fin (n + 2)))
              (by simp) F) r⟩ =
        ⟨(nerve C).σ j ((nerve C).δ (0 : Fin (n + 2)) F),
          transportL (leftσ_eq (n := n) ((nerve C).δ (0 : Fin (n + 2)) F))
            (transportL (leftδ_zero_eq (n := n) F).symm
              (L.map (F.map' 0 1 (Nat.zero_le 1) (Nat.succ_le_succ (Nat.zero_le _))) l)),
          transportR (rightσ_eq (n := n) ((nerve C).δ (0 : Fin (n + 2)) F))
            (transportR (rightδ_of_val_ne_last (n := n) (i := (0 : Fin (n + 2)))
              (by simp) F) r)⟩ := by
      rfl
    have hFinalL : ((nerve C).δ (0 : Fin ((n + 1) + 2)) ((nerve C).σ j.succ F)).left =
        ((nerve C).σ j ((nerve C).δ (0 : Fin (n + 2)) F)).left :=
      congrArg (fun G => G.left) hChain
    have hFinalR : ((nerve C).δ (0 : Fin ((n + 1) + 2)) ((nerve C).σ j.succ F)).right =
        ((nerve C).σ j ((nerve C).δ (0 : Fin (n + 2)) F)).right :=
      congrArg (fun G => G.right) hChain
    have hPairAuxFD :
        ∀ {X0 XM ZL1 ZL2 Y0 YR1 ZR1 YR2 ZR2 : C} (x : L.obj X0) (y : R.obj (op Y0))
          (f : X0 ⟶ XM)
        (e1 : X0 = X0) (e2 : XM = ZL1) (e3 : XM = XM) (e4 : XM = ZL2) (hT : ZL1 = ZL2)
        (er1 : Y0 = YR1) (er2 : YR1 = ZR1) (er3 : Y0 = YR2) (er4 : YR2 = ZR2) (hTR : ZR1 = ZR2),
        (transportL e2 (L.map f (transportL e1 x)), transportR er2 (transportR er1 y)) =
        cast (by cases hT; cases hTR; rfl)
          (transportL e4 (transportL e3 (L.map f x)),
            transportR er4 (transportR er3 y)) := by
      intro X0 XM ZL1 ZL2 Y0 YR1 ZR1 YR2 ZR2 x y f e1 e2 e3 e4 hT er1 er2 er3 er4 hTR
      cases e1
      cases e3
      cases e2
      cases hT
      cases e4
      cases er1
      cases er3
      cases er2
      cases hTR
      cases er4
      rfl
    have hEq := hPairAuxFD l r (F.map' 0 1 (Nat.zero_le 1) (Nat.succ_le_succ (Nat.zero_le _)))
      (leftσ_eq (n := n + 1) (i := j.succ) F)
      ((leftδ_zero_eq (n := n + 1) ((nerve C).σ j.succ F)).symm)
      ((leftδ_zero_eq (n := n) F).symm)
      (leftσ_eq (n := n) (i := j) ((nerve C).δ (0 : Fin (n + 2)) F))
      hFinalL
      (rightσ_eq (n := n + 1) (i := j.succ) F)
      (rightδ_of_val_ne_last (n := n + 1) (i := (0 : Fin ((n + 1) + 2))) (by simp)
        ((nerve C).σ j.succ F))
      (rightδ_of_val_ne_last (n := n) (i := (0 : Fin (n + 2))) (by simp) F)
      (rightσ_eq (n := n) (i := j) ((nerve C).δ (0 : Fin (n + 2)) F))
      hFinalR
    have hCoeffHEq :
        (transportL ((leftδ_zero_eq (n := n + 1) ((nerve C).σ j.succ F)).symm)
          (L.map (F.map' 0 1 (Nat.zero_le 1) (Nat.succ_le_succ (Nat.zero_le _)))
            (transportL (leftσ_eq (n := n + 1) (i := j.succ) F) l)),
          transportR
            (rightδ_of_val_ne_last (n := n + 1) (i := (0 : Fin ((n + 1) + 2))) (by simp)
              ((nerve C).σ j.succ F))
            (transportR (rightσ_eq (n := n + 1) (i := j.succ) F) r)) ≍
        (transportL (leftσ_eq (n := n) (i := j) ((nerve C).δ (0 : Fin (n + 2)) F))
          (transportL ((leftδ_zero_eq (n := n) F).symm)
            (L.map (F.map' 0 1 (Nat.zero_le 1) (Nat.succ_le_succ (Nat.zero_le _))) l)),
          transportR (rightσ_eq (n := n) (i := j) ((nerve C).δ (0 : Fin (n + 2)) F))
            (transportR (rightδ_of_val_ne_last (n := n) (i := (0 : Fin (n + 2))) (by simp) F) r)) :=
      hEq ▸ cast_heq _ _
    rw [hOuterL, hOuterR]
    exact Sigma.ext hChain hCoeffHEq
  · have hChain := nerve_δ_comp_σ_of_le (n := n)
      (i := qi.castSucc.succ) (j := j) h F
    have hIc : (qi.castSucc.succ).castSucc =
        (⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ := by
      apply Fin.ext
      simp [Fin.val_castSucc, Fin.val_succ]
    rw [hIc] at hChain ⊢
    have hqiLt : qi.val < n := qi.isLt
    set y : barObj C R L (n + 1) := ⟨F, l, r⟩ with hy
    have hFaceL : F.left = ((nerve C).δ qi.castSucc.succ F).left :=
      leftδ_of_val_ne_zero (n := n) (i := qi.castSucc.succ)
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega) F
    have hFaceR : F.right = ((nerve C).δ qi.castSucc.succ F).right :=
      rightδ_of_val_ne_last (n := n) (i := qi.castSucc.succ)
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega) F
    have hInner : barδ qi.castSucc.succ y =
        ⟨(nerve C).δ qi.castSucc.succ F,
          transportL hFaceL l, transportR hFaceR r⟩ := by
      rw [barδ_castSucc_succ_eq (n := n) qi y, hy]
      rfl
    have hSigL : F.left = ((nerve C).σ j.succ F).left :=
      leftσ_eq (n := n + 1) (i := j.succ) F
    have hSigR : F.right = ((nerve C).σ j.succ F).right :=
      rightσ_eq (n := n + 1) (i := j.succ) F
    have hSigma : barσ j.succ y =
        ⟨(nerve C).σ j.succ F,
          transportL hSigL l, transportR hSigR r⟩ := by
      rw [hy]
      rfl
    set zS : barObj C R L (n + 2) :=
      ⟨(nerve C).σ j.succ F,
        transportL hSigL l, transportR hSigR r⟩ with hzSdef
    set zR : barObj C R L n :=
      ⟨(nerve C).δ qi.castSucc.succ F,
        transportL hFaceL l, transportR hFaceR r⟩ with hzRdef
    have hzS : barσ j.succ y = zS := by
      rw [hzSdef]
      exact hSigma
    have hzR : barδ qi.castSucc.succ y = zR := by
      rw [hzRdef]
      exact hInner
    rw [hzS, hzR]
    have hOutL : ((nerve C).σ j.succ F).left =
        ((nerve C).δ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ)
          ((nerve C).σ j.succ F)).left :=
      leftδ_of_val_ne_zero (n := n + 1)
        (i := ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ))
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega)
        ((nerve C).σ j.succ F)
    have hOutR : ((nerve C).σ j.succ F).right =
        ((nerve C).δ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ)
          ((nerve C).σ j.succ F)).right :=
      rightδ_of_val_ne_last (n := n + 1)
        (i := ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ))
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega)
        ((nerve C).σ j.succ F)
    have hSigOutL : ((nerve C).δ qi.castSucc.succ F).left =
        ((nerve C).σ j ((nerve C).δ qi.castSucc.succ F)).left :=
      leftσ_eq (n := n) (i := j) ((nerve C).δ qi.castSucc.succ F)
    have hSigOutR : ((nerve C).δ qi.castSucc.succ F).right =
        ((nerve C).σ j ((nerve C).δ qi.castSucc.succ F)).right :=
      rightσ_eq (n := n) (i := j) ((nerve C).δ qi.castSucc.succ F)
    have hOuterL : barδ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ) zS =
        ⟨(nerve C).δ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ)
          ((nerve C).σ j.succ F),
          transportL hOutL (transportL hSigL l),
          transportR hOutR (transportR hSigR r)⟩ := by
      rw [barδ_castSucc_succ_eq (n := n + 1)
        (⟨qi.val, by omega⟩ : Fin (n + 1)) zS, hzSdef]
      rfl
    have hOuterR : barσ j zR =
        ⟨(nerve C).σ j ((nerve C).δ qi.castSucc.succ F),
          transportL hSigOutL (transportL hFaceL l),
          transportR hSigOutR (transportR hFaceR r)⟩ := by
      rw [hzRdef]
      rfl
    have hFinalL : ((nerve C).δ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ)
        ((nerve C).σ j.succ F)).left =
        ((nerve C).σ j ((nerve C).δ qi.castSucc.succ F)).left :=
      congrArg (fun G => G.left) hChain
    have hFinalR : ((nerve C).δ ((⟨qi.val, by omega⟩ : Fin (n + 1)).castSucc.succ)
        ((nerve C).σ j.succ F)).right =
        ((nerve C).σ j ((nerve C).δ qi.castSucc.succ F)).right :=
      congrArg (fun G => G.right) hChain
    have hPairAux : ∀ {X0 XL1 ZL1 XL2 ZL2 Y0 YR1 ZR1 YR2 ZR2 : C}
        (x : L.obj X0) (y : R.obj (op Y0))
        (e1 : X0 = XL1) (e2 : XL1 = ZL1) (e3 : X0 = XL2) (e4 : XL2 = ZL2)
        (hT : ZL1 = ZL2)
        (er1 : Y0 = YR1) (er2 : YR1 = ZR1) (er3 : Y0 = YR2) (er4 : YR2 = ZR2)
        (hTR : ZR1 = ZR2),
        (transportL e2 (transportL e1 x), transportR er2 (transportR er1 y)) =
        cast (by cases hT; cases hTR; rfl)
          (transportL e4 (transportL e3 x), transportR er4 (transportR er3 y)) := by
      intro X0 XL1 ZL1 XL2 ZL2 Y0 YR1 ZR1 YR2 ZR2 x y e1 e2 e3 e4 hT er1 er2 er3 er4 hTR
      cases e1
      cases e3
      cases e2
      cases hT
      cases e4
      cases er1
      cases er3
      cases er2
      cases hTR
      cases er4
      rfl
    have hEq := hPairAux l r hSigL hOutL hFaceL hSigOutL hFinalL hSigR hOutR hFaceR hSigOutR hFinalR
    have hCoeffHEq :
        (transportL hOutL (transportL hSigL l),
          transportR hOutR (transportR hSigR r)) ≍
        (transportL hSigOutL (transportL hFaceL l),
          transportR hSigOutR (transportR hFaceR r)) :=
      hEq ▸ cast_heq _ _
    rw [hOuterL, hOuterR]
    exact Sigma.ext hChain hCoeffHEq
  · have hval : (Fin.last (n + 1) : Fin (n + 2)).val ≤ (j.castSucc : Fin (n + 2)).val := h
    rw [Fin.val_last, Fin.val_castSucc] at hval
    have hj := j.isLt
    omega

/-- Face-degeneracy identity: zero and interior via `L.map_id`. -/
theorem δ_comp_σ_self {n : ℕ} {i : Fin (n + 1)} (x : barObj C R L n) :
    barδ (R := R) (L := L) i.castSucc (barσ i x) = x := by
  obtain ⟨F, l, r⟩ := x
  have hi := fin_zero_succ (n := n) i
  rcases hi with rfl | ⟨q, rfl⟩
  · have hChain := nerve_δ_comp_σ_self (n := n) (i := (0 : Fin (n + 1))) F
    have hIc : (0 : Fin (n + 1)).castSucc = (0 : Fin (n + 2)) := by
      apply Fin.ext
      simp
    rw [hIc] at hChain ⊢
    set S : ComposableArrows C (n + 1) := (nerve C).σ (0 : Fin (n + 1)) F
    set y : barObj C R L n := ⟨F, l, r⟩ with hy
    have hSigL : F.left = S.left :=
      leftσ_eq (n := n) (i := (0 : Fin (n + 1))) F
    have hSigR : F.right = S.right :=
      rightσ_eq (n := n) (i := (0 : Fin (n + 1))) F
    have hSigma : barσ (0 : Fin (n + 1)) y =
        ⟨S, transportL hSigL l, transportR hSigR r⟩ := by
      rw [hy]
      rfl
    set zS : barObj C R L (n + 1) :=
      ⟨S, transportL hSigL l, transportR hSigR r⟩ with hzSdef
    have hzS : barσ (0 : Fin (n + 1)) y = zS := by
      rw [hzSdef]
      exact hSigma
    have hOuterL0 : S.obj' 1 =
        ((nerve C).δ (0 : Fin (n + 2)) S).left :=
      (leftδ_zero_eq (n := n) S).symm
    have hOuterR0 : S.right =
        ((nerve C).δ (0 : Fin (n + 2)) S).right :=
      rightδ_of_val_ne_last (n := n) (i := (0 : Fin (n + 2))) (by simp)
        S
    have hOuter : barδ (0 : Fin (n + 2)) zS =
        ⟨(nerve C).δ (0 : Fin (n + 2)) S,
          transportL hOuterL0
            (L.map (S.map' 0 1)
              (transportL hSigL l)),
          transportR hOuterR0 (transportR hSigR r)⟩ := by
      rw [barδ_zero_eq (n := n) zS, hzSdef]
      rfl
    have hFinalL : ((nerve C).δ (0 : Fin (n + 2))
        S).left = F.left :=
      congrArg (fun G => G.left) hChain
    have hFinalR : ((nerve C).δ (0 : Fin (n + 2))
        S).right = F.right :=
      congrArg (fun G => G.right) hChain
    have hS01 : S.map' 0 1 = F.map' 0 0 := rfl
    have hId : F.map' 0 0 = 𝟙 _ := ComposableArrows.map'_self F 0
    have hMid : F.left = S.obj' 1 := hSigL
    have hActEq : L.map (S.map' 0 1)
        (transportL hSigL l) = transportL hMid l := by
      rw [transportL_map hSigL (S.map' 0 1) l]
      have hMor : eqToHom hSigL ≫ S.map' 0 1 = eqToHom hMid := by
        rw [hS01, hId]
        change eqToHom hSigL ≫ 𝟙 S.left = eqToHom hMid
        rw [Category.comp_id]
        rfl
      rw [hMor, eqToHom_map L hMid]
      rfl
    have hPairAuxSelf0 : ∀ {X0 XS XD ZL1 ZL2 Y0 YS ZR1 ZR2 : C}
        (x : L.obj X0) (y : R.obj (op Y0))
        (fS : XS ⟶ XD)
        (eSig : X0 = XS) (eMid : X0 = XD) (eOut : XD = ZL1) (eTgt : X0 = ZL2)
        (hT : ZL1 = ZL2)
        (erSig : Y0 = YS) (erOut : YS = ZR1) (erTgt : Y0 = ZR2)
        (hTR : ZR1 = ZR2)
        (hAct : L.map fS (transportL eSig x) = transportL eMid x),
        (transportL eOut (L.map fS (transportL eSig x)),
          transportR erOut (transportR erSig y)) =
        cast (by cases hT; cases hTR; rfl)
          (transportL eTgt x, transportR erTgt y) := by
      intro X0 XS XD ZL1 ZL2 Y0 YS ZR1 ZR2 x y fS eSig eMid eOut eTgt hT
        erSig erOut erTgt hTR hAct
      rw [hAct]
      cases eMid
      cases eOut
      cases eTgt
      cases hT
      cases erSig
      cases erOut
      cases erTgt
      cases hTR
      rfl
    have hEq := hPairAuxSelf0 l r (S.map' 0 1)
      hSigL hMid hOuterL0 rfl hFinalL
      hSigR hOuterR0 rfl hFinalR
      hActEq
    have hCoeffHEq :
        (transportL hOuterL0
          (L.map (S.map' 0 1)
            (transportL hSigL l)),
          transportR hOuterR0 (transportR hSigR r)) ≍ (l, r) :=
      hEq ▸ cast_heq _ _
    rw [hzS, hOuter]
    exact Sigma.ext hChain hCoeffHEq
  · have hChain := nerve_δ_comp_σ_self (n := n) (i := q.succ) F
    have hIc : (q.succ).castSucc = (⟨q.val, by omega⟩ : Fin n).castSucc.succ := by
      apply Fin.ext
      simp [Fin.val_castSucc, Fin.val_succ]
    rw [hIc] at hChain ⊢
    set y : barObj C R L n := ⟨F, l, r⟩ with hy
    have hSigL : F.left = ((nerve C).σ q.succ F).left :=
      leftσ_eq (n := n) (i := q.succ) F
    have hSigR : F.right = ((nerve C).σ q.succ F).right :=
      rightσ_eq (n := n) (i := q.succ) F
    have hSigma : barσ q.succ y =
        ⟨(nerve C).σ q.succ F,
          transportL hSigL l, transportR hSigR r⟩ := by
      rw [hy]
      rfl
    set zS : barObj C R L (n + 1) :=
      ⟨(nerve C).σ q.succ F,
        transportL hSigL l, transportR hSigR r⟩ with hzSdef
    have hzS : barσ q.succ y = zS := by
      rw [hzSdef]
      exact hSigma
    have hOutL : ((nerve C).σ q.succ F).left =
        ((nerve C).δ ((⟨q.val, by omega⟩ : Fin n).castSucc.succ)
          ((nerve C).σ q.succ F)).left :=
      leftδ_of_val_ne_zero (n := n)
        (i := ((⟨q.val, by omega⟩ : Fin n).castSucc.succ))
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega)
        ((nerve C).σ q.succ F)
    have hOutR : ((nerve C).σ q.succ F).right =
        ((nerve C).δ ((⟨q.val, by omega⟩ : Fin n).castSucc.succ)
          ((nerve C).σ q.succ F)).right :=
      rightδ_of_val_ne_last (n := n)
        (i := ((⟨q.val, by omega⟩ : Fin n).castSucc.succ))
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega)
        ((nerve C).σ q.succ F)
    have hOuter : barδ ((⟨q.val, by omega⟩ : Fin n).castSucc.succ) zS =
        ⟨(nerve C).δ ((⟨q.val, by omega⟩ : Fin n).castSucc.succ)
          ((nerve C).σ q.succ F),
          transportL hOutL (transportL hSigL l),
          transportR hOutR (transportR hSigR r)⟩ := by
      rw [barδ_castSucc_succ_eq (n := n)
        (⟨q.val, by omega⟩ : Fin n) zS, hzSdef]
      rfl
    have hFinalL : ((nerve C).δ ((⟨q.val, by omega⟩ : Fin n).castSucc.succ)
        ((nerve C).σ q.succ F)).left = F.left :=
      congrArg (fun G => G.left) hChain
    have hFinalR : ((nerve C).δ ((⟨q.val, by omega⟩ : Fin n).castSucc.succ)
        ((nerve C).σ q.succ F)).right = F.right :=
      congrArg (fun G => G.right) hChain
    have hPairAuxSelf : ∀ {X0 XL1 ZL1 XL2 ZL2 Y0 YR1 ZR1 YR2 ZR2 : C}
        (x : L.obj X0) (y : R.obj (op Y0))
        (e1 : X0 = XL1) (e2 : XL1 = ZL1) (e3 : X0 = XL2) (e4 : XL2 = ZL2)
        (hT : ZL1 = ZL2)
        (er1 : Y0 = YR1) (er2 : YR1 = ZR1) (er3 : Y0 = YR2) (er4 : YR2 = ZR2)
        (hTR : ZR1 = ZR2),
        (transportL e2 (transportL e1 x), transportR er2 (transportR er1 y)) =
        cast (by cases hT; cases hTR; rfl)
          (transportL e4 (transportL e3 x), transportR er4 (transportR er3 y)) := by
      intro X0 XL1 ZL1 XL2 ZL2 Y0 YR1 ZR1 YR2 ZR2 x y e1 e2 e3 e4 hT er1 er2 er3 er4 hTR
      cases e1
      cases e3
      cases e2
      cases hT
      cases e4
      cases er1
      cases er3
      cases er2
      cases hTR
      cases er4
      rfl
    have hEq := hPairAuxSelf l r hSigL hOutL rfl rfl hFinalL hSigR hOutR rfl rfl hFinalR
    have hCoeffHEq :
        (transportL hOutL (transportL hSigL l),
          transportR hOutR (transportR hSigR r)) ≍ (l, r) :=
      hEq ▸ cast_heq _ _
    rw [hzS, hOuter]
    exact Sigma.ext hChain hCoeffHEq

/-- Face-degeneracy above-identity: interior and last via `R.map_id`. -/
theorem δ_comp_σ_succ {n : ℕ} {i : Fin (n + 1)} (x : barObj C R L n) :
    barδ (R := R) (L := L) i.succ (barσ i x) = x := by
  obtain ⟨F, l, r⟩ := x
  have hi := fin_last_castSucc (n := n) i
  rcases hi with rfl | ⟨q, rfl⟩
  · have hChain := nerve_δ_comp_σ_succ (n := n) (i := Fin.last n) F
    have hIs : (Fin.last n).succ = Fin.last (n + 1) := rfl
    rw [hIs] at hChain ⊢
    set y : barObj C R L n := ⟨F, l, r⟩ with hy
    set S : ComposableArrows C (n + 1) := (nerve C).σ (Fin.last n) F with hSdef
    have hSigL : F.left = S.left :=
      leftσ_eq (n := n) (i := Fin.last n) F
    have hSigR : F.right = S.right :=
      rightσ_eq (n := n) (i := Fin.last n) F
    have hSigma : barσ (Fin.last n) y =
        ⟨S, transportL hSigL l, transportR hSigR r⟩ := by
      rw [hy]
      rfl
    set zS : barObj C R L (n + 1) :=
      ⟨S, transportL hSigL l, transportR hSigR r⟩ with hzSdef
    have hzS : barσ (Fin.last n) y = zS := by
      rw [hzSdef]
      exact hSigma
    have hCastN : (⟨n, by omega⟩ : Fin (n + 2)) = (Fin.last n).castSucc := by
      apply Fin.ext
      simp [Fin.val_last, Fin.val_castSucc]
    have hMidR : F.right = S.obj' n := by
      rw [hSdef]
      change F.obj (⟨n, by omega⟩ : Fin (n + 1)) =
        ((nerve C).σ (Fin.last n) F).obj (⟨n, by omega⟩ : Fin (n + 2))
      rw [CategoryTheory.nerve.σ_obj, hCastN, Fin.predAbove_last_castSucc]
      rfl
    have hObjEq : S.obj' n = S.right := hMidR.symm.trans hSigR
    have hCastLast : (⟨n + 1, by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) := by
      apply Fin.ext
      simp [Fin.val_last]
    have hFinEq : (Fin.last n).predAbove (⟨n, by omega⟩ : Fin (n + 2)) =
        (Fin.last n).predAbove (⟨n + 1, by omega⟩ : Fin (n + 2)) := by
      rw [hCastN, hCastLast, Fin.predAbove_last_castSucc, Fin.predAbove_right_last]
    have hThin : (SimplexCategory.toCat.map (SimplexCategory.σ (Fin.last n))).toFunctor.map
        (homOfLE (by omega : n ≤ n + 1) :
          (⟨n, by omega⟩ : Fin (n + 2)) ⟶ (⟨n + 1, by omega⟩ : Fin (n + 2))) =
        eqToHom hFinEq :=
      (Preorder.subsingleton_hom (α := Fin (n + 1)) _ _).elim _ _
    have hDegMap : S.map' n (n + 1) = eqToHom hObjEq := by
      have e1 : S.map' n (n + 1) = F.map (eqToHom hFinEq) := by
        change S.map (homOfLE (by omega : n ≤ n + 1) :
          (⟨n, by omega⟩ : Fin (n + 2)) ⟶ (⟨n + 1, by omega⟩ : Fin (n + 2))) = _
        change F.map ((SimplexCategory.toCat.map (SimplexCategory.σ (Fin.last n))).toFunctor.map
          (homOfLE (by omega : n ≤ n + 1) :
            (⟨n, by omega⟩ : Fin (n + 2)) ⟶ (⟨n + 1, by omega⟩ : Fin (n + 2)))) = _
        rw [hThin]
        rfl
      have e2 : F.map (eqToHom hFinEq) = eqToHom (congrArg F.obj hFinEq) :=
        eqToHom_map F hFinEq
      rw [e1]
      exact e2.trans rfl
    have hMorR : S.map' n (n + 1) ≫ eqToHom hSigR.symm = eqToHom hMidR.symm := by
      rw [hDegMap, eqToHom_trans]
    have hRMapEq : R.map ((eqToHom hMidR.symm).op) r = transportR hMidR r := by
      have hGen : ∀ {X Y : C} (h : X = Y) (x : R.obj (op X)),
          R.map ((eqToHom h.symm).op) x = transportR h x := by
        intro X Y h x
        cases h
        simp [transportR]
      exact hGen hMidR r
    have hActR : R.map ((S.map' n (n + 1)).op) (transportR hSigR r) =
        transportR hMidR r := by
      rw [transportR_map hSigR (S.map' n (n + 1)) r, hMorR]
      exact hRMapEq
    have hOuterL : S.left = ((nerve C).δ (Fin.last (n + 1)) S).left := by
      apply leftδ_of_val_ne_zero (n := n) (F := S)
      simp [Fin.val_last]
    have hOuterR : S.obj' n = ((nerve C).δ (Fin.last (n + 1)) S).right :=
      (rightδ_last_eq (n := n) S).symm
    have hOuter : barδ (Fin.last (n + 1)) zS =
        ⟨(nerve C).δ (Fin.last (n + 1)) S,
          transportL hOuterL (transportL hSigL l),
          transportR hOuterR (R.map ((S.map' n (n + 1)).op) (transportR hSigR r))⟩ := by
      rw [barδ_last_eq (n := n) zS, hzSdef]
      rfl
    have hFinalL : ((nerve C).δ (Fin.last (n + 1)) S).left = F.left :=
      congrArg (fun G => G.left) hChain
    have hFinalR : ((nerve C).δ (Fin.last (n + 1)) S).right = F.right :=
      congrArg (fun G => G.right) hChain
    have hPairAuxLast : ∀ {X0 XL1 ZL1 ZL2 Y0 YS YD ZR1 ZR2 : C}
        (x : L.obj X0) (y : R.obj (op Y0))
        (eSigL : X0 = XL1) (eOutL : XL1 = ZL1) (eTgtL : X0 = ZL2)
        (hT : ZL1 = ZL2)
        (fS : YD ⟶ YS)
        (eSigR : Y0 = YS) (eMidR : Y0 = YD) (eOutR : YD = ZR1) (eTgtR : Y0 = ZR2)
        (hTR : ZR1 = ZR2)
        (hAct : R.map fS.op (transportR eSigR y) = transportR eMidR y),
        (transportL eOutL (transportL eSigL x),
          transportR eOutR (R.map fS.op (transportR eSigR y))) =
        cast (by cases hT; cases hTR; rfl)
          (transportL eTgtL x, transportR eTgtR y) := by
      intro X0 XL1 ZL1 ZL2 Y0 YS YD ZR1 ZR2 x y eSigL eOutL eTgtL hT
        fS eSigR eMidR eOutR eTgtR hTR hAct
      rw [hAct]
      cases eSigL
      cases eOutL
      cases eTgtL
      cases hT
      cases eMidR
      cases eOutR
      cases eTgtR
      cases hTR
      rfl
    have hEq := hPairAuxLast l r hSigL hOuterL rfl hFinalL
      (S.map' n (n + 1)) hSigR hMidR hOuterR rfl hFinalR hActR
    have hCoeffHEq :
        (transportL hOuterL (transportL hSigL l),
          transportR hOuterR (R.map ((S.map' n (n + 1)).op) (transportR hSigR r))) ≍ (l, r) :=
      hEq ▸ cast_heq _ _
    rw [hzS, hOuter]
    exact Sigma.ext hChain hCoeffHEq
  · have hChain := nerve_δ_comp_σ_succ (n := n) (i := q.castSucc) F
    have hIs : (q.castSucc).succ = (⟨q.val, by omega⟩ : Fin n).castSucc.succ := by
      apply Fin.ext
      simp [Fin.val_succ, Fin.val_castSucc]
    rw [hIs] at hChain ⊢
    set y : barObj C R L n := ⟨F, l, r⟩ with hy
    set S : ComposableArrows C (n + 1) := (nerve C).σ q.castSucc F
    have hSigL : F.left = S.left :=
      leftσ_eq (n := n) (i := q.castSucc) F
    have hSigR : F.right = S.right :=
      rightσ_eq (n := n) (i := q.castSucc) F
    have hSigma : barσ q.castSucc y =
        ⟨S, transportL hSigL l, transportR hSigR r⟩ := by
      rw [hy]
      rfl
    set zS : barObj C R L (n + 1) :=
      ⟨S, transportL hSigL l, transportR hSigR r⟩ with hzSdef
    have hzS : barσ q.castSucc y = zS := by
      rw [hzSdef]
      exact hSigma
    have hOutL : S.left =
        ((nerve C).δ ((⟨q.val, by omega⟩ : Fin n).castSucc.succ) S).left :=
      leftδ_of_val_ne_zero (n := n)
        (i := ((⟨q.val, by omega⟩ : Fin n).castSucc.succ))
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega)
        S
    have hOutR : S.right =
        ((nerve C).δ ((⟨q.val, by omega⟩ : Fin n).castSucc.succ) S).right :=
      rightδ_of_val_ne_last (n := n)
        (i := ((⟨q.val, by omega⟩ : Fin n).castSucc.succ))
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega)
        S
    have hOuter : barδ ((⟨q.val, by omega⟩ : Fin n).castSucc.succ) zS =
        ⟨(nerve C).δ ((⟨q.val, by omega⟩ : Fin n).castSucc.succ) S,
          transportL hOutL (transportL hSigL l),
          transportR hOutR (transportR hSigR r)⟩ := by
      rw [barδ_castSucc_succ_eq (n := n)
        (⟨q.val, by omega⟩ : Fin n) zS, hzSdef]
      rfl
    have hFinalL : ((nerve C).δ ((⟨q.val, by omega⟩ : Fin n).castSucc.succ) S).left =
        F.left :=
      congrArg (fun G => G.left) hChain
    have hFinalR : ((nerve C).δ ((⟨q.val, by omega⟩ : Fin n).castSucc.succ) S).right =
        F.right :=
      congrArg (fun G => G.right) hChain
    have hPairAuxSucc : ∀ {X0 XL1 ZL1 XL2 ZL2 Y0 YR1 ZR1 YR2 ZR2 : C}
        (x : L.obj X0) (y : R.obj (op Y0))
        (e1 : X0 = XL1) (e2 : XL1 = ZL1) (e3 : X0 = XL2) (e4 : XL2 = ZL2)
        (hT : ZL1 = ZL2)
        (er1 : Y0 = YR1) (er2 : YR1 = ZR1) (er3 : Y0 = YR2) (er4 : YR2 = ZR2)
        (hTR : ZR1 = ZR2),
        (transportL e2 (transportL e1 x), transportR er2 (transportR er1 y)) =
        cast (by cases hT; cases hTR; rfl)
          (transportL e4 (transportL e3 x), transportR er4 (transportR er3 y)) := by
      intro X0 XL1 ZL1 XL2 ZL2 Y0 YR1 ZR1 YR2 ZR2 x y e1 e2 e3 e4 hT er1 er2 er3 er4 hTR
      cases e1
      cases e3
      cases e2
      cases hT
      cases e4
      cases er1
      cases er3
      cases er2
      cases hTR
      cases er4
      rfl
    have hEq := hPairAuxSucc l r hSigL hOutL rfl rfl hFinalL hSigR hOutR rfl rfl hFinalR
    have hCoeffHEq :
        (transportL hOutL (transportL hSigL l),
          transportR hOutR (transportR hSigR r)) ≍ (l, r) :=
      hEq ▸ cast_heq _ _
    rw [hzS, hOuter]
    exact Sigma.ext hChain hCoeffHEq

/-- Face-degeneracy above: interior and last live, zero impossible. -/
theorem δ_comp_σ_of_gt {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : j.castSucc < i) (x : barObj C R L (n + 1)) :
    barδ (R := R) (L := L) i.succ (barσ j.castSucc x) =
      barσ (R := R) (L := L) j (barδ i x) := by
  obtain ⟨F, l, r⟩ := x
  have hi := fin_tri (n := n) i
  rcases hi with rfl | ⟨qi, rfl⟩ | rfl
  · have hval : (j.castSucc : Fin (n + 2)).val < (0 : Fin (n + 2)).val := h
    rw [Fin.val_castSucc, Fin.val_zero] at hval
    omega
  · have hChain := nerve_δ_comp_σ_of_gt (n := n)
      (i := qi.castSucc.succ) (j := j) h F
    have hIs : (qi.castSucc.succ).succ =
        (⟨qi.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ := by
      apply Fin.ext
      simp [Fin.val_succ, Fin.val_castSucc]
    rw [hIs] at hChain ⊢
    set y : barObj C R L (n + 1) := ⟨F, l, r⟩ with hy
    have hFaceL : F.left = ((nerve C).δ qi.castSucc.succ F).left :=
      leftδ_of_val_ne_zero (n := n) (i := qi.castSucc.succ)
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega) F
    have hFaceR : F.right = ((nerve C).δ qi.castSucc.succ F).right :=
      rightδ_of_val_ne_last (n := n) (i := qi.castSucc.succ)
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega) F
    have hInner : barδ qi.castSucc.succ y =
        ⟨(nerve C).δ qi.castSucc.succ F,
          transportL hFaceL l, transportR hFaceR r⟩ := by
      rw [barδ_castSucc_succ_eq (n := n) qi y, hy]
      rfl
    have hSigL : F.left = ((nerve C).σ j.castSucc F).left :=
      leftσ_eq (n := n + 1) (i := j.castSucc) F
    have hSigR : F.right = ((nerve C).σ j.castSucc F).right :=
      rightσ_eq (n := n + 1) (i := j.castSucc) F
    have hSigma : barσ j.castSucc y =
        ⟨(nerve C).σ j.castSucc F,
          transportL hSigL l, transportR hSigR r⟩ := by
      rw [hy]
      rfl
    set zS : barObj C R L (n + 2) :=
      ⟨(nerve C).σ j.castSucc F,
        transportL hSigL l, transportR hSigR r⟩ with hzSdef
    set zR : barObj C R L n :=
      ⟨(nerve C).δ qi.castSucc.succ F,
        transportL hFaceL l, transportR hFaceR r⟩ with hzRdef
    have hzS : barσ j.castSucc y = zS := by
      rw [hzSdef]
      exact hSigma
    have hzR : barδ qi.castSucc.succ y = zR := by
      rw [hzRdef]
      exact hInner
    rw [hzS, hzR]
    have hOutL : ((nerve C).σ j.castSucc F).left =
        ((nerve C).δ ((⟨qi.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ)
          ((nerve C).σ j.castSucc F)).left :=
      leftδ_of_val_ne_zero (n := n + 1)
        (i := ((⟨qi.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ))
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega)
        ((nerve C).σ j.castSucc F)
    have hOutR : ((nerve C).σ j.castSucc F).right =
        ((nerve C).δ ((⟨qi.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ)
          ((nerve C).σ j.castSucc F)).right :=
      rightδ_of_val_ne_last (n := n + 1)
        (i := ((⟨qi.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ))
        (by rw [Fin.val_succ, Fin.val_castSucc]; omega)
        ((nerve C).σ j.castSucc F)
    have hSigOutL : ((nerve C).δ qi.castSucc.succ F).left =
        ((nerve C).σ j ((nerve C).δ qi.castSucc.succ F)).left :=
      leftσ_eq (n := n) (i := j) ((nerve C).δ qi.castSucc.succ F)
    have hSigOutR : ((nerve C).δ qi.castSucc.succ F).right =
        ((nerve C).σ j ((nerve C).δ qi.castSucc.succ F)).right :=
      rightσ_eq (n := n) (i := j) ((nerve C).δ qi.castSucc.succ F)
    have hOuter : barδ ((⟨qi.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ) zS =
        ⟨(nerve C).δ ((⟨qi.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ)
          ((nerve C).σ j.castSucc F),
          transportL hOutL (transportL hSigL l),
          transportR hOutR (transportR hSigR r)⟩ := by
      rw [barδ_castSucc_succ_eq (n := n + 1)
        (⟨qi.val + 1, by omega⟩ : Fin (n + 1)) zS, hzSdef]
      rfl
    have hOuterR : barσ j zR =
        ⟨(nerve C).σ j ((nerve C).δ qi.castSucc.succ F),
          transportL hSigOutL (transportL hFaceL l),
          transportR hSigOutR (transportR hFaceR r)⟩ := by
      rw [hzRdef]
      rfl
    have hFinalL : ((nerve C).δ ((⟨qi.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ)
        ((nerve C).σ j.castSucc F)).left =
        ((nerve C).σ j ((nerve C).δ qi.castSucc.succ F)).left :=
      congrArg (fun G => G.left) hChain
    have hFinalR : ((nerve C).δ ((⟨qi.val + 1, by omega⟩ : Fin (n + 1)).castSucc.succ)
        ((nerve C).σ j.castSucc F)).right =
        ((nerve C).σ j ((nerve C).δ qi.castSucc.succ F)).right :=
      congrArg (fun G => G.right) hChain
    have hPairAux : ∀ {X0 XL1 ZL1 XL2 ZL2 Y0 YR1 ZR1 YR2 ZR2 : C}
        (x : L.obj X0) (y : R.obj (op Y0))
        (e1 : X0 = XL1) (e2 : XL1 = ZL1) (e3 : X0 = XL2) (e4 : XL2 = ZL2)
        (hT : ZL1 = ZL2)
        (er1 : Y0 = YR1) (er2 : YR1 = ZR1) (er3 : Y0 = YR2) (er4 : YR2 = ZR2)
        (hTR : ZR1 = ZR2),
        (transportL e2 (transportL e1 x), transportR er2 (transportR er1 y)) =
        cast (by cases hT; cases hTR; rfl)
          (transportL e4 (transportL e3 x), transportR er4 (transportR er3 y)) := by
      intro X0 XL1 ZL1 XL2 ZL2 Y0 YR1 ZR1 YR2 ZR2 x y e1 e2 e3 e4 hT er1 er2 er3 er4 hTR
      cases e1
      cases e3
      cases e2
      cases hT
      cases e4
      cases er1
      cases er3
      cases er2
      cases hTR
      cases er4
      rfl
    have hEq := hPairAux l r hSigL hOutL hFaceL hSigOutL hFinalL hSigR hOutR hFaceR hSigOutR hFinalR
    have hCoeffHEq :
        (transportL hOutL (transportL hSigL l),
          transportR hOutR (transportR hSigR r)) ≍
        (transportL hSigOutL (transportL hFaceL l),
          transportR hSigOutR (transportR hFaceR r)) :=
      hEq ▸ cast_heq _ _
    rw [hOuter, hOuterR]
    exact Sigma.ext hChain hCoeffHEq
  · have hChain := nerve_δ_comp_σ_of_gt (n := n)
      (i := Fin.last (n + 1)) (j := j) h F
    have hIs : (Fin.last (n + 1)).succ = Fin.last (n + 2) := rfl
    rw [hIs] at hChain ⊢
    set y : barObj C R L (n + 1) := ⟨F, l, r⟩ with hy
    set S : ComposableArrows C (n + 2) := (nerve C).σ j.castSucc F with hSdef
    have hSigL : F.left = S.left := by
      rw [hSdef]
      exact leftσ_eq F
    have hSigR : F.right = S.right := by
      rw [hSdef]
      exact rightσ_eq F
    have hFaceL : F.left = ((nerve C).δ (Fin.last (n + 1)) F).left := by
      apply leftδ_of_val_ne_zero
      simp [Fin.val_last]
    have hFaceR : F.obj' n = ((nerve C).δ (Fin.last (n + 1)) F).right :=
      (rightδ_last_eq F).symm
    have hSigma : barσ j.castSucc y =
        ⟨S, transportL hSigL l, transportR hSigR r⟩ := by
      rw [hy]
      rfl
    have hInner : barδ (Fin.last (n + 1)) y =
        ⟨(nerve C).δ (Fin.last (n + 1)) F, transportL hFaceL l,
          transportR hFaceR (R.map (Quiver.Hom.op (F.map' n (n + 1))) r)⟩ := by
      rw [barδ_last_eq y, hy]
      rfl
    set zS : barObj C R L (n + 2) :=
      ⟨S, transportL hSigL l, transportR hSigR r⟩ with hzSdef
    set zR : barObj C R L n :=
      ⟨(nerve C).δ (Fin.last (n + 1)) F, transportL hFaceL l,
        transportR hFaceR (R.map (Quiver.Hom.op (F.map' n (n + 1))) r)⟩ with hzRdef
    have hzS : barσ j.castSucc y = zS := by
      rw [hzSdef]
      exact hSigma
    have hzR : barδ (Fin.last (n + 1)) y = zR := by
      rw [hzRdef]
      exact hInner
    rw [hzS, hzR]
    have hOutL : S.left =
        ((nerve C).δ (Fin.last (n + 2)) S).left := by
      apply leftδ_of_val_ne_zero
      simp [Fin.val_last]
    have hOutR : S.obj' (n + 1) =
        ((nerve C).δ (Fin.last (n + 2)) S).right :=
      (rightδ_last_eq S).symm
    have hSigOutL : ((nerve C).δ (Fin.last (n + 1)) F).left =
        ((nerve C).σ j ((nerve C).δ (Fin.last (n + 1)) F)).left :=
      leftσ_eq _
    have hSigOutR : ((nerve C).δ (Fin.last (n + 1)) F).right =
        ((nerve C).σ j ((nerve C).δ (Fin.last (n + 1)) F)).right :=
      rightσ_eq _
    have hOuter : barδ (Fin.last (n + 2)) zS =
        ⟨(nerve C).δ (Fin.last (n + 2)) S,
          transportL hOutL (transportL hSigL l),
          transportR hOutR (R.map (((S.map' (n + 1) (n + 2)).op))
            (transportR hSigR r))⟩ := by
      rw [barδ_last_eq zS, hzSdef]
      rfl
    have hOuterR : barσ j zR =
        ⟨(nerve C).σ j ((nerve C).δ (Fin.last (n + 1)) F),
          transportL hSigOutL (transportL hFaceL l),
          transportR hSigOutR (transportR hFaceR
            (R.map (Quiver.Hom.op (F.map' n (n + 1))) r))⟩ := by
      rw [hzRdef]
      rfl
    have hjLt : j.val < n + 1 := by
      have hj := h
      rw [Fin.lt_def, Fin.val_castSucc, Fin.val_last] at hj
      exact hj
    have hMidR : F.obj' n = S.obj' (n + 1) := by
      change F.obj ⟨n, Nat.lt_succ_of_le (Nat.le_succ n)⟩ =
        S.obj ⟨n + 1, Nat.lt_succ_of_le (Nat.le_succ (n + 1))⟩
      rw [hSdef, CategoryTheory.nerve.σ_obj]
      have hPred : j.castSucc.predAbove
          (⟨n + 1, Nat.lt_succ_of_le (Nat.le_succ (n + 1))⟩ : Fin (n + 3)) =
          (⟨n, Nat.lt_succ_of_le (Nat.le_succ n)⟩ : Fin (n + 2)) := by
        have hlt : j.castSucc.castSucc <
            (⟨n + 1, Nat.lt_succ_of_le (Nat.le_succ (n + 1))⟩ : Fin (n + 3)) := by
          rw [Fin.lt_def, Fin.val_castSucc, Fin.val_castSucc]
          change j.val < n + 1
          exact hjLt
        rw [Fin.predAbove_of_castSucc_lt _ _ hlt]
        rfl
      rw [hPred]
    have hA2 : (⟨n + 2, Nat.lt_succ_self (n + 2)⟩ : Fin (n + 3)) =
        Fin.last (n + 2) := by
      apply Fin.ext
      simp [Fin.val_last]
    have hP2 : j.castSucc.predAbove
        (⟨n + 2, Nat.lt_succ_self (n + 2)⟩ : Fin (n + 3)) =
        (⟨n + 1, Nat.lt_succ_self (n + 1)⟩ : Fin (n + 2)) := by
      rw [hA2, Fin.predAbove_right_last]
      rfl
    have hP1 : j.castSucc.predAbove
        (⟨n + 1, Nat.lt_succ_of_le (Nat.le_succ (n + 1))⟩ : Fin (n + 3)) =
        (⟨n, Nat.lt_succ_of_le (Nat.le_succ n)⟩ : Fin (n + 2)) := by
      have hlt : j.castSucc.castSucc <
          (⟨n + 1, Nat.lt_succ_of_le (Nat.le_succ (n + 1))⟩ : Fin (n + 3)) := by
        rw [Fin.lt_def, Fin.val_castSucc, Fin.val_castSucc]
        change j.val < n + 1
        exact hjLt
      rw [Fin.predAbove_of_castSucc_lt _ _ hlt]
      rfl
    have hleA : (⟨n + 1, Nat.lt_succ_of_le (Nat.le_succ (n + 1))⟩ : Fin (n + 3)) ≤
        (⟨n + 2, Nat.lt_succ_self (n + 2)⟩ : Fin (n + 3)) :=
      Fin.mk_le_mk.mpr (Nat.le_succ (n + 1))
    have hleB : (⟨n, Nat.lt_succ_of_le (Nat.le_succ n)⟩ : Fin (n + 2)) ≤
        (⟨n + 1, Nat.lt_succ_self (n + 1)⟩ : Fin (n + 2)) :=
      Fin.mk_le_mk.mpr (Nat.le_succ n)
    have hleP : j.castSucc.predAbove
        (⟨n + 1, Nat.lt_succ_of_le (Nat.le_succ (n + 1))⟩ : Fin (n + 3)) ≤
        j.castSucc.predAbove
          (⟨n + 2, Nat.lt_succ_self (n + 2)⟩ : Fin (n + 3)) := by
      rw [hP1, hP2]
      exact Fin.mk_le_mk.mpr (Nat.le_succ n)
    have hThinP : (SimplexCategory.toCat.map (SimplexCategory.σ j.castSucc)).toFunctor.map
        (homOfLE hleA :
          (⟨n + 1, Nat.lt_succ_of_le (Nat.le_succ (n + 1))⟩ : Fin (n + 3)) ⟶
          (⟨n + 2, Nat.lt_succ_self (n + 2)⟩ : Fin (n + 3))) =
        homOfLE hleP :=
      (Preorder.subsingleton_hom (α := Fin (n + 2)) _ _).elim _ _
    have eS : S.map' (n + 1) (n + 2) =
        F.map (homOfLE hleP) := by
      change S.map (homOfLE hleA :
        (⟨n + 1, Nat.lt_succ_of_le (Nat.le_succ (n + 1))⟩ : Fin (n + 3)) ⟶
        (⟨n + 2, Nat.lt_succ_self (n + 2)⟩ : Fin (n + 3))) = _
      change F.map ((SimplexCategory.toCat.map (SimplexCategory.σ j.castSucc)).toFunctor.map
        (homOfLE hleA :
          (⟨n + 1, Nat.lt_succ_of_le (Nat.le_succ (n + 1))⟩ : Fin (n + 3)) ⟶
          (⟨n + 2, Nat.lt_succ_self (n + 2)⟩ : Fin (n + 3)))) = _
      rw [hThinP]
      rfl
    have hCommFin : homOfLE hleP ≫
        eqToHom hP2 =
        eqToHom hP1 ≫ homOfLE hleB :=
      (Preorder.subsingleton_hom (α := Fin (n + 2)) _ _).elim _ _
    have hEqP1 : F.map (eqToHom hP1) = eqToHom (congrArg F.obj hP1) :=
      eqToHom_map F hP1
    have hEqP2 : F.map (eqToHom hP2) = eqToHom (congrArg F.obj hP2) :=
      eqToHom_map F hP2
    have hFmapEq : F.map (homOfLE hleB :
        (⟨n, Nat.lt_succ_of_le (Nat.le_succ n)⟩ : Fin (n + 2)) ⟶
        (⟨n + 1, Nat.lt_succ_self (n + 1)⟩ : Fin (n + 2))) =
        F.map' n (n + 1) := rfl
    have hMidEq : eqToHom (congrArg F.obj hP1) = eqToHom hMidR.symm := rfl
    have hSigEq : eqToHom (congrArg F.obj hP2) = eqToHom hSigR.symm := rfl
    have hMorR : S.map' (n + 1) (n + 2) ≫
        eqToHom hSigR.symm =
        eqToHom hMidR.symm ≫ F.map' n (n + 1) := by
      rw [← hMidEq, ← hSigEq, eS, ← hEqP1, ← hEqP2, ← hFmapEq]
      have hCon : F.map (homOfLE hleP ≫ eqToHom hP2) =
          F.map (eqToHom hP1 ≫ homOfLE hleB) :=
        congrArg F.map hCommFin
      rw [F.map_comp, F.map_comp] at hCon
      exact hCon
    have hRMapEq : R.map ((eqToHom hMidR.symm).op)
        (R.map (Quiver.Hom.op (F.map' n (n + 1))) r) =
        transportR hMidR (R.map (Quiver.Hom.op (F.map' n (n + 1))) r) := by
      have hGen : ∀ {X Y : C} (h : X = Y) (x : R.obj (op X)),
          R.map ((eqToHom h.symm).op) x = transportR h x := by
        intro X Y h x
        cases h
        simp [transportR]
      exact hGen hMidR _
    have hActR : R.map (((S.map' (n + 1) (n + 2)).op))
        (transportR hSigR r) =
        transportR hMidR (R.map (Quiver.Hom.op (F.map' n (n + 1))) r) := by
      rw [transportR_map hSigR ((S.map' (n + 1) (n + 2))) r,
        hMorR]
      change R.map ((eqToHom hMidR.symm ≫ F.map' n (n + 1)).op) r = _
      rw [op_comp, Functor.map_comp]
      exact hRMapEq
    have hOuterN : barδ (Fin.last (n + 2)) zS =
        ⟨(nerve C).δ (Fin.last (n + 2)) S,
          transportL hOutL (transportL hSigL l),
          transportR hOutR (transportR hMidR
            (R.map (Quiver.Hom.op (F.map' n (n + 1))) r))⟩ := by
      rw [hOuter, hActR]
    have hFinalL : ((nerve C).δ (Fin.last (n + 2)) S).left =
        ((nerve C).σ j ((nerve C).δ (Fin.last (n + 1)) F)).left :=
      congrArg (fun G => G.left) hChain
    have hFinalR : ((nerve C).δ (Fin.last (n + 2)) S).right =
        ((nerve C).σ j ((nerve C).δ (Fin.last (n + 1)) F)).right :=
      congrArg (fun G => G.right) hChain
    have hPairAux : ∀ {X0 XL1 ZL1 XL2 ZL2 Y0 YR1 ZR1 YR2 ZR2 : C}
        (x : L.obj X0) (y : R.obj (op Y0))
        (e1 : X0 = XL1) (e2 : XL1 = ZL1) (e3 : X0 = XL2) (e4 : XL2 = ZL2)
        (hT : ZL1 = ZL2)
        (er1 : Y0 = YR1) (er2 : YR1 = ZR1) (er3 : Y0 = YR2) (er4 : YR2 = ZR2)
        (hTR : ZR1 = ZR2),
        (transportL e2 (transportL e1 x), transportR er2 (transportR er1 y)) =
        cast (by cases hT; cases hTR; rfl)
          (transportL e4 (transportL e3 x), transportR er4 (transportR er3 y)) := by
      intro X0 XL1 ZL1 XL2 ZL2 Y0 YR1 ZR1 YR2 ZR2 x y e1 e2 e3 e4 hT er1 er2 er3 er4 hTR
      cases e1
      cases e3
      cases e2
      cases hT
      cases e4
      cases er1
      cases er3
      cases er2
      cases hTR
      cases er4
      rfl
    have hEq := hPairAux l (R.map (Quiver.Hom.op (F.map' n (n + 1))) r)
      hSigL hOutL hFaceL hSigOutL hFinalL hMidR hOutR hFaceR hSigOutR hFinalR
    have hCoeffHEq :
        (transportL hOutL (transportL hSigL l),
          transportR hOutR (transportR hMidR
            (R.map (Quiver.Hom.op (F.map' n (n + 1))) r))) ≍
        (transportL hSigOutL (transportL hFaceL l),
          transportR hSigOutR (transportR hFaceR
            (R.map (Quiver.Hom.op (F.map' n (n + 1))) r))) :=
      hEq ▸ cast_heq _ _
    rw [hOuterN, hOuterR]
    exact Sigma.ext hChain hCoeffHEq

/-- Degeneracy-degeneracy identity. -/
theorem σ_comp_σ {n : ℕ} {i j : Fin (n + 1)} (h : i ≤ j)
    (x : barObj C R L n) :
    barσ (R := R) (L := L) i.castSucc (barσ j x) =
      barσ (R := R) (L := L) j.succ (barσ i x) := by
  obtain ⟨F, l, r⟩ := x
  have hChain : (nerve C).σ i.castSucc ((nerve C).σ j F) =
      (nerve C).σ j.succ ((nerve C).σ i F) :=
    nerve_σ_comp_σ h F
  have hF1L : F.left = ((nerve C).σ j F).left := leftσ_eq F
  have hF2L : ((nerve C).σ j F).left =
      ((nerve C).σ i.castSucc ((nerve C).σ j F)).left :=
    leftσ_eq _
  have hG1L : F.left = ((nerve C).σ i F).left := leftσ_eq F
  have hG2L : ((nerve C).σ i F).left =
      ((nerve C).σ j.succ ((nerve C).σ i F)).left :=
    leftσ_eq _
  have hF1R : F.right = ((nerve C).σ j F).right := rightσ_eq F
  have hF2R : ((nerve C).σ j F).right =
      ((nerve C).σ i.castSucc ((nerve C).σ j F)).right :=
    rightσ_eq _
  have hG1R : F.right = ((nerve C).σ i F).right := rightσ_eq F
  have hG2R : ((nerve C).σ i F).right =
      ((nerve C).σ j.succ ((nerve C).σ i F)).right :=
    rightσ_eq _
  have hLHS : barσ (R := R) (L := L) i.castSucc (barσ j ⟨F, l, r⟩) =
      ⟨(nerve C).σ i.castSucc ((nerve C).σ j F),
        transportL hF2L (transportL hF1L l),
        transportR hF2R (transportR hF1R r)⟩ := by
    have e1 : barσ (R := R) (L := L) j ⟨F, l, r⟩ =
        ⟨(nerve C).σ j F, transportL hF1L l, transportR hF1R r⟩ := rfl
    rw [e1]
    have e2 : barσ (R := R) (L := L) i.castSucc
          ⟨(nerve C).σ j F, transportL hF1L l, transportR hF1R r⟩ =
        ⟨(nerve C).σ i.castSucc ((nerve C).σ j F),
          transportL hF2L (transportL hF1L l),
          transportR hF2R (transportR hF1R r)⟩ := rfl
    rw [e2]
  have hRHS : barσ (R := R) (L := L) j.succ (barσ i ⟨F, l, r⟩) =
      ⟨(nerve C).σ j.succ ((nerve C).σ i F),
        transportL hG2L (transportL hG1L l),
        transportR hG2R (transportR hG1R r)⟩ := by
    have e1 : barσ (R := R) (L := L) i ⟨F, l, r⟩ =
        ⟨(nerve C).σ i F, transportL hG1L l, transportR hG1R r⟩ := rfl
    rw [e1]
    have e2 : barσ (R := R) (L := L) j.succ
          ⟨(nerve C).σ i F, transportL hG1L l, transportR hG1R r⟩ =
        ⟨(nerve C).σ j.succ ((nerve C).σ i F),
          transportL hG2L (transportL hG1L l),
          transportR hG2R (transportR hG1R r)⟩ := rfl
    rw [e2]
  have hFinalL : ((nerve C).σ i.castSucc ((nerve C).σ j F)).left =
      ((nerve C).σ j.succ ((nerve C).σ i F)).left :=
    congrArg (fun G => G.left) hChain
  have hFinalR : ((nerve C).σ i.castSucc ((nerve C).σ j F)).right =
      ((nerve C).σ j.succ ((nerve C).σ i F)).right :=
    congrArg (fun G => G.right) hChain
  have hPairAux : ∀ {X0 XL1 ZL1 XL2 ZL2 Y0 YR1 ZR1 YR2 ZR2 : C}
      (x : L.obj X0) (y : R.obj (op Y0))
      (e1 : X0 = XL1) (e2 : XL1 = ZL1) (e3 : X0 = XL2) (e4 : XL2 = ZL2)
      (hT : ZL1 = ZL2)
      (er1 : Y0 = YR1) (er2 : YR1 = ZR1) (er3 : Y0 = YR2) (er4 : YR2 = ZR2)
      (hTR : ZR1 = ZR2),
      (transportL e2 (transportL e1 x), transportR er2 (transportR er1 y)) =
      cast (by cases hT; cases hTR; rfl)
        (transportL e4 (transportL e3 x), transportR er4 (transportR er3 y)) := by
    intro X0 XL1 ZL1 XL2 ZL2 Y0 YR1 ZR1 YR2 ZR2 x y e1 e2 e3 e4 hT er1 er2 er3 er4 hTR
    cases e1
    cases e3
    cases e2
    cases hT
    cases e4
    cases er1
    cases er3
    cases er2
    cases hTR
    cases er4
    rfl
  have hEq := hPairAux l r hF1L hF2L hG1L hG2L hFinalL hF1R hF2R hG1R hG2R hFinalR
  have hCoeffHEq :
      (transportL hF2L (transportL hF1L l),
        transportR hF2R (transportR hF1R r)) ≍
      (transportL hG2L (transportL hG1L l),
        transportR hG2R (transportR hG1R r)) :=
    hEq ▸ cast_heq _ _
  rw [hLHS, hRHS]
  exact Sigma.ext hChain hCoeffHEq

end BarLaws

/-- Category bar data with explicit `TypeCat` promotion.

Faces and degeneracies are the `Type`-morphisms `↾(barδ i)` and `↾(barσ i)`.
Identity fields close by `ext x` over the public `BarLaws` witnesses, so the
public literal depends only on public laws; transports stay private. -/
noncomputable def categoryBarData : SimplicialObject.Data (Type (max u v uL uR)) :=
  { obj := barObj C R L
    δ := fun {n} i => ↾(barδ (R := R) (L := L) i)
    σ := fun {n} i => ↾(barσ (R := R) (L := L) i)
    δ_comp_δ := fun {n} {i j} h => by
      ext x
      exact BarLaws.δ_comp_δ h x
    δ_comp_σ_of_le := fun {n} {i j} h => by
      ext x
      exact BarLaws.δ_comp_σ_of_le h x
    δ_comp_σ_self := fun {n} {i} => by
      ext x
      exact BarLaws.δ_comp_σ_self x
    δ_comp_σ_succ := fun {n} {i} => by
      ext x
      exact BarLaws.δ_comp_σ_succ x
    δ_comp_σ_of_gt := fun {n} {i j} h => by
      ext x
      exact BarLaws.δ_comp_σ_of_gt h x
    σ_comp_σ := fun {n} {i j} h => by
      ext x
      exact BarLaws.σ_comp_σ h x }

/-- Category bar as a simplicial set. -/
noncomputable def categoryBar : SSet.{max u v uL uR} :=
  SimplicialObject.Data.toSimplicialObject (categoryBarData (C := C) (R := R) (L := L))

/-- Stable degree-zero equivalence: pairs over the same object. -/
noncomputable def barObjZeroEquiv :
    barObj C R L 0 ≃ Σ x : C, (L.obj x × R.obj (op x)) where
  toFun
    | ⟨F, l, r⟩ => ⟨F.obj 0, l, r⟩
  invFun
    | ⟨x, l, r⟩ => ⟨ComposableArrows.mk₀ x, l, r⟩
  left_inv := by
    rintro ⟨F, l, r⟩
    have hChain : ComposableArrows.mk₀ (F.obj 0) = F := by
      refine Functor.ext ?_ ?_
      · intro j
        have hj : j = 0 := Fin.eq_zero j
        rw [hj]
        rfl
      · intro j k f
        have hj : j = 0 := Fin.eq_zero j
        have hk : k = 0 := Fin.eq_zero k
        subst hj
        subst hk
        have hf : f = 𝟙 (0 : Fin 1) := Subsingleton.elim f _
        rw [hf, Functor.map_id, Functor.map_id]
        simp only [eqToHom_trans, eqToHom_refl, Category.id_comp]
    refine Sigma.ext hChain ?_
    exact HEq.rfl
  right_inv := by
    rintro ⟨x, l, r⟩
    rfl

/-- Projection to the underlying chain. -/
def barChain {n : ℕ} (x : barObj C R L n) : ComposableArrows C n := x.1

/-- Projection to the left coefficient. -/
def barCoeffL {n : ℕ} (x : barObj C R L n) : L.obj x.1.left := x.2.1

/-- Projection to the right coefficient. -/
def barCoeffR {n : ℕ} (x : barObj C R L n) : R.obj (op x.1.right) := x.2.2

/-- `d₀` on a `mk₁` chain acts by `L` on the arrow. -/
theorem barδ_zero_mk₁ {X₀ X₁ : C} (f : X₀ ⟶ X₁) (l : L.obj (ComposableArrows.mk₁ f).left)
    (r : R.obj (op (ComposableArrows.mk₁ f).right)) :
    barδ (0 : Fin 2) (⟨ComposableArrows.mk₁ f, l, r⟩ : barObj C R L 1) =
      ⟨(nerve C).δ 0 (ComposableArrows.mk₁ f),
        cast (congrArg L.obj (rfl : (ComposableArrows.mk₁ f).obj' 1 =
          ((nerve C).δ (0 : Fin 2) (ComposableArrows.mk₁ f)).left))
          (L.map ((ComposableArrows.mk₁ f).map' 0 1) l),
        cast (congrArg (fun Z => R.obj (op Z)) (by
            change (ComposableArrows.mk₁ f).obj ⟨1, by omega⟩ =
              ((nerve C).δ (0 : Fin 2) (ComposableArrows.mk₁ f)).obj (Fin.last _)
            rw [CategoryTheory.nerve.δ_obj]
            congr 1))
          r⟩ := by
  set p : barObj C R L 1 := ⟨ComposableArrows.mk₁ f, l, r⟩ with hp
  change barδ (0 : Fin (0 + 2)) p = (_ : barObj C R L 0)
  rw [barδ_zero_eq (n := 0) p, hp]

/-- `d_last` on a `mk₁` chain acts by `R` on the arrow. -/
theorem barδ_last_mk₁ {X₀ X₁ : C} (f : X₀ ⟶ X₁) (l : L.obj (ComposableArrows.mk₁ f).left)
    (r : R.obj (op (ComposableArrows.mk₁ f).right)) :
    barδ (Fin.last 1) (⟨ComposableArrows.mk₁ f, l, r⟩ : barObj C R L 1) =
      ⟨(nerve C).δ (Fin.last 1) (ComposableArrows.mk₁ f),
        cast (congrArg L.obj (by
            change (ComposableArrows.mk₁ f).obj ⟨0, by omega⟩ =
              ((nerve C).δ (Fin.last 1) (ComposableArrows.mk₁ f)).obj (0 : Fin _)
            rw [CategoryTheory.nerve.δ_obj]
            congr 1))
          l,
        cast (congrArg (fun Z => R.obj (op Z)) (by
            have h : ((nerve C).δ (Fin.last 1) (ComposableArrows.mk₁ f)).obj (Fin.last _) =
                (ComposableArrows.mk₁ f).obj ⟨0, by omega⟩ := by
              rw [CategoryTheory.nerve.δ_obj]
              congr 1
            exact h.symm))
          (R.map (Quiver.Hom.op ((ComposableArrows.mk₁ f).map' 0 1)) r)⟩ := by
  set p : barObj C R L 1 := ⟨ComposableArrows.mk₁ f, l, r⟩ with hp
  change barδ (Fin.last (0 + 1)) p = (_ : barObj C R L 0)
  rw [barδ_last_eq (n := 0) p, hp]

/-- `s₀` on a `mk₀` chain inserts an identity. -/
theorem barσ_zero_mk₀ (X : C) (l : L.obj (ComposableArrows.mk₀ X).left)
    (r : R.obj (op (ComposableArrows.mk₀ X).right)) (i : Fin 1) :
    barσ i (⟨ComposableArrows.mk₀ X, l, r⟩ : barObj C R L 0) =
      ⟨(nerve C).σ i (ComposableArrows.mk₀ X),
        cast (congrArg L.obj (by
            change (ComposableArrows.mk₀ X).obj ⟨0, by omega⟩ =
              ((nerve C).σ i (ComposableArrows.mk₀ X)).obj (0 : Fin _)
            rw [CategoryTheory.nerve.σ_obj]
            exact congrArg _ Fin.predAbove_right_zero.symm)) l,
        cast (congrArg (fun Z => R.obj (op Z)) (by
            change (ComposableArrows.mk₀ X).obj ⟨0, by omega⟩ =
              ((nerve C).σ i (ComposableArrows.mk₀ X)).obj (Fin.last _)
            rw [CategoryTheory.nerve.σ_obj]
            congr 1
            exact Fin.predAbove_right_last.symm)) r⟩ := by
  rfl

@[simp]
theorem categoryBarData_obj (n : ℕ) :
    (categoryBarData (C := C) (R := R) (L := L)).obj n = barObj C R L n :=
  rfl

@[simp]
theorem categoryBarData_δ {n : ℕ} (i : Fin (n + 2)) :
    (categoryBarData (C := C) (R := R) (L := L)).δ i =
      ↾(barδ (R := R) (L := L) i) :=
  rfl

@[simp]
theorem categoryBarData_σ {n : ℕ} (i : Fin (n + 1)) :
    (categoryBarData (C := C) (R := R) (L := L)).σ i =
      ↾(barσ (R := R) (L := L) i) :=
  rfl

@[simp]
theorem categoryBar_obj (n : ℕ) :
    (categoryBar (C := C) (R := R) (L := L)).obj (op (SimplexCategory.mk n)) =
      barObj C R L n :=
  rfl

@[simp]
theorem categoryBar_map_δ {n : ℕ} (i : Fin (n + 2)) :
    (categoryBar (C := C) (R := R) (L := L)).map (SimplexCategory.δ i).op =
      ↾(barδ (R := R) (L := L) i) := by
  simp [categoryBar, SimplicialObject.Data.toSimplicialObject_map_δ]

@[simp]
theorem categoryBar_map_σ {n : ℕ} (i : Fin (n + 1)) :
    (categoryBar (C := C) (R := R) (L := L)).map (SimplexCategory.σ i).op =
      ↾(barσ (R := R) (L := L) i) := by
  simp [categoryBar, SimplicialObject.Data.toSimplicialObject_map_σ]

end CategoryBar

end CategoryTheory
