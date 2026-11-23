/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module


import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import MathlibExt.AlgebraicTopology.SimplicialSet.EdgewiseResolution

/-!
# Rowwise edgewise-resolution regression tests

These tests pin the reversed total-décalage carrier, the literal right-block
augmentation and its diagonal square, and the ordinary extra degeneracy on
each fixed-inner row.  They also record the `δ 0` obstruction preventing the
row sections from assembling into one global extra degeneracy in `SSet`.

No realization, weak-equivalence, topology, outer-bisimplicial, Quillen,
Stage, basepoint, or global extra-degeneracy claim is made.
-/

open CategoryTheory Opposite SimplexCategory

open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.EdgewiseResolutionTests

-- Carrier and variance computations.
example (X : SSet.{u}) (p q : SimplexCategoryᵒᵖ) :
    ((SSet.edgewiseResolution X).left.obj p).obj q =
      X.obj (op (AugmentedSimplexCategory.tensorObjOf p.unop q.unop)) :=
  SSet.edgewiseResolution_left_obj_obj X p q

example (X : SSet.{u}) (p : SimplexCategoryᵒᵖ)
    {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) :
    ((SSet.edgewiseResolution X).left.obj p).map f =
      X.map (AugmentedSimplexCategory.tensorHomOf
        (𝟙 p.unop) f.unop).op :=
  SSet.edgewiseResolution_left_obj_map X p f

example (X : SSet.{u}) {p r : SimplexCategoryᵒᵖ} (f : p ⟶ r)
    (q : SimplexCategoryᵒᵖ) :
    ((SSet.edgewiseResolution X).left.map f).app q =
      X.map (AugmentedSimplexCategory.tensorHomOf
        (SimplexCategory.rev.map f.unop) (𝟙 q.unop)).op :=
  SSet.edgewiseResolution_left_map_app X f q

-- The diagonal uses `rev(f) ⊕ f`, not the swapped orientation.
example (X : SSet.{u}) {p r : SimplexCategoryᵒᵖ} (f : p ⟶ r) :
    (SSet.simplicialDiagonalFunctor.obj
        (SSet.edgewiseResolution X).left).map f ≫
        (SSet.edgewiseResolutionDiagonalIso X).hom.app r =
      (SSet.edgewiseResolutionDiagonalIso X).hom.app p ≫
        (SSet.esd.obj X).map f :=
  (SSet.edgewiseResolutionDiagonalIso X).hom.naturality f

example (X : SSet.{u}) {p r : SimplexCategoryᵒᵖ} (f : p ⟶ r) :
    (SSet.esd.obj X).map f =
      X.map (AugmentedSimplexCategory.tensorHomOf
        (SimplexCategory.rev.map f.unop) f.unop).op :=
  rfl

-- The augmentation is literally the right block and selects target `δ 0`.
example (X : SSet.{u}) (p q : SimplexCategoryᵒᵖ) :
    ((SSet.edgewiseResolution X).hom.app p).app q =
      X.map (AugmentedSimplexCategory.inr' p.unop q.unop).op :=
  SSet.edgewiseResolution_hom_app_app X p q

example (X : SSet.{u}) (x : X.obj (op ⦋1⦌)) :
    ((SSet.edgewiseResolution X).hom.app (op ⦋0⦌)).app (op ⦋0⦌) x =
      X.δ 0 x := by
  rw [SSet.edgewiseResolution_hom_app_app]
  change X.map (SimplexCategory.edgewiseRightInclusion.app ⦋0⦌).op x = _
  rw [SimplexCategory.edgewiseRightInclusion_app_zero]
  rfl

-- The exact diagonal square identifies the raw comparison, not an alternate map.
example (X : SSet.{u}) :
    (SSet.edgewiseResolutionDiagonalIso X).hom ≫
        SSet.esdComparison.app X =
      SSet.simplicialDiagonalFunctor.map
          (SSet.edgewiseResolution X).hom ≫
        (SSet.diagonalConstIso X).hom :=
  SSet.edgewiseResolution_diagonal_augmentation X

-- Both identity-component isomorphisms have their canonical round trips.
example (X : SSet.{u}) :
    (SSet.edgewiseResolutionDiagonalIso X).hom ≫
        (SSet.edgewiseResolutionDiagonalIso X).inv = 𝟙 _ ∧
      (SSet.edgewiseResolutionDiagonalIso X).inv ≫
        (SSet.edgewiseResolutionDiagonalIso X).hom = 𝟙 _ :=
  ⟨(SSet.edgewiseResolutionDiagonalIso X).hom_inv_id,
    (SSet.edgewiseResolutionDiagonalIso X).inv_hom_id⟩

example (X : SSet.{u}) :
    (SSet.diagonalConstIso X).hom ≫ (SSet.diagonalConstIso X).inv = 𝟙 _ ∧
      (SSet.diagonalConstIso X).inv ≫ (SSet.diagonalConstIso X).hom = 𝟙 _ :=
  ⟨(SSet.diagonalConstIso X).hom_inv_id,
    (SSet.diagonalConstIso X).inv_hom_id⟩

-- Fixed rows are exactly the transposed augmentation rows.
example (X : SSet.{u}) (q : SimplexCategoryᵒᵖ) :
    (SSet.edgewiseResolutionRow X q).left =
      ((CategoryTheory.SimplicialObject.transposeFunctor (Type u)).obj
        (SSet.edgewiseResolution X).left).obj q :=
  SSet.edgewiseResolutionRow_left X q

example (X : SSet.{u}) (q : SimplexCategoryᵒᵖ) :
    (SSet.edgewiseResolutionRow X q).hom =
      ((CategoryTheory.SimplicialObject.transposeFunctor (Type u)).map
        (SSet.edgewiseResolution X).hom).app q :=
  SSet.edgewiseResolutionRow_hom X q

-- Exact fixed-row section and boundary-degeneracy computations.
example (X : SSet.{u}) (m : ℕ) :
    (SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋m⦌)).s' =
      X.map (SSet.edgewiseBoundarySection m).op :=
  SSet.edgewiseResolutionRowExtraDegeneracy_s' X m

example (X : SSet.{u}) (m n : ℕ) :
    (SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋m⦌)).s n =
      X.map (SSet.edgewiseBoundaryDegeneracy n m).op :=
  SSet.edgewiseResolutionRowExtraDegeneracy_s X m n

-- All five ordinary extra-degeneracy identities, generic in the fixed inner
-- degree and outer degree (hence including `0`, `1`, and `2`).
example (X : SSet.{u}) (m : ℕ) :
    let ed := SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋m⦌)
    ed.s' ≫ (SSet.edgewiseResolutionRow X (op ⦋m⦌)).hom.app (op ⦋0⦌) =
      𝟙 (SSet.edgewiseResolutionRow X (op ⦋m⦌)).right :=
  (SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋m⦌)).s'_comp_ε

example (X : SSet.{u}) (m : ℕ) :
    let R := SSet.edgewiseResolutionRow X (op ⦋m⦌)
    let ed := SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋m⦌)
    ed.s 0 ≫ R.left.δ 1 = R.hom.app (op ⦋0⦌) ≫ ed.s' :=
  (SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋m⦌)).s₀_comp_δ₁

example (X : SSet.{u}) (m n : ℕ) :
    let R := SSet.edgewiseResolutionRow X (op ⦋m⦌)
    let ed := SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋m⦌)
    ed.s n ≫ R.left.δ 0 = 𝟙 _ :=
  (SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋m⦌)).s_comp_δ₀ n

example (X : SSet.{u}) (m n : ℕ) (i : Fin (n + 2)) :
    let R := SSet.edgewiseResolutionRow X (op ⦋m⦌)
    let ed := SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋m⦌)
    ed.s (n + 1) ≫ R.left.δ i.succ = R.left.δ i ≫ ed.s n :=
  (SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋m⦌)).s_comp_δ n i

example (X : SSet.{u}) (m n : ℕ) (i : Fin (n + 1)) :
    let R := SSet.edgewiseResolutionRow X (op ⦋m⦌)
    let ed := SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋m⦌)
    ed.s n ≫ R.left.σ i.succ = R.left.σ i ≫ ed.s (n + 1) :=
  (SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋m⦌)).s_comp_σ n i

/-- The five row identities collected at fixed inner and outer degrees. -/
def rowFiveIdentities (X : SSet.{u}) (m n : ℕ) : Prop :=
  let R := SSet.edgewiseResolutionRow X (op ⦋m⦌)
  let ed := SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋m⦌)
  ed.s' ≫ R.hom.app (op ⦋0⦌) = 𝟙 R.right ∧
    ed.s 0 ≫ R.left.δ 1 = R.hom.app (op ⦋0⦌) ≫ ed.s' ∧
    ed.s n ≫ R.left.δ 0 = 𝟙 _ ∧
    (∀ i : Fin (n + 2),
      ed.s (n + 1) ≫ R.left.δ i.succ = R.left.δ i ≫ ed.s n) ∧
    (∀ i : Fin (n + 1),
      ed.s n ≫ R.left.σ i.succ = R.left.σ i ≫ ed.s (n + 1))

example (X : SSet.{u}) : rowFiveIdentities X 0 0 := by
  exact ⟨(SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋0⦌)).s'_comp_ε,
    (SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋0⦌)).s₀_comp_δ₁,
    (SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋0⦌)).s_comp_δ₀ 0,
    (SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋0⦌)).s_comp_δ 0,
    (SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋0⦌)).s_comp_σ 0⟩

example (X : SSet.{u}) : rowFiveIdentities X 1 1 := by
  exact ⟨(SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋1⦌)).s'_comp_ε,
    (SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋1⦌)).s₀_comp_δ₁,
    (SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋1⦌)).s_comp_δ₀ 1,
    (SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋1⦌)).s_comp_δ 1,
    (SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋1⦌)).s_comp_σ 1⟩

example (X : SSet.{u}) : rowFiveIdentities X 2 2 := by
  exact ⟨(SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋2⦌)).s'_comp_ε,
    (SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋2⦌)).s₀_comp_δ₁,
    (SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋2⦌)).s_comp_δ₀ 2,
    (SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋2⦌)).s_comp_δ 2,
    (SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋2⦌)).s_comp_σ 2⟩

-- Explicit inner degrees and outer degrees `0`, `1`, and `2` consume the
-- public computations rather than a hypothetical global contraction.
example (X : SSet.{u}) :
    (SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋0⦌)).s 0 =
        X.map (SSet.edgewiseBoundaryDegeneracy 0 0).op ∧
      (SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋1⦌)).s 1 =
        X.map (SSet.edgewiseBoundaryDegeneracy 1 1).op ∧
      (SSet.edgewiseResolutionRowExtraDegeneracy X (op ⦋2⦌)).s 2 =
        X.map (SSet.edgewiseBoundaryDegeneracy 2 2).op :=
  ⟨SSet.edgewiseResolutionRowExtraDegeneracy_s X 0 0,
    SSet.edgewiseResolutionRowExtraDegeneracy_s X 1 1,
    SSet.edgewiseResolutionRowExtraDegeneracy_s X 2 2⟩

-- The `δ 0` Yoneda obstruction: the boundary sections do not assemble
-- naturally in the inner simplex variable.
def innerNaturalityLeft : ⦋1⦌ ⟶ ⦋1⦌ :=
  AugmentedSimplexCategory.tensorHomOf
      (𝟙 ⦋0⦌) (SimplexCategory.δ (0 : Fin 2)) ≫
    SSet.edgewiseBoundarySection 1

def innerNaturalityRight : ⦋1⦌ ⟶ ⦋1⦌ :=
  SSet.edgewiseBoundarySection 0 ≫
    SimplexCategory.δ (0 : Fin 2)

example : innerNaturalityLeft ≠ innerNaturalityRight := by decide

def deltaOneIdentity : Δ[1].obj (op ⦋1⦌) :=
  SSet.stdSimplex.objEquiv.symm
    (SimplexCategory.Hom.mk OrderHom.id : ⦋1⦌ ⟶ ⦋1⦌)

example :
    Δ[1].map innerNaturalityLeft.op deltaOneIdentity ≠
      Δ[1].map innerNaturalityRight.op deltaOneIdentity := by
  intro h
  have h' := SSet.stdSimplex.objEquiv.symm.injective h
  exact (by decide : innerNaturalityLeft ≠ innerNaturalityRight) h'

-- On the identity edge of `Δ[1]`, the ordinary distinguished face is valid,
-- while the right-handed terminal-face identity is observably false.
example :
    let R := SSet.edgewiseResolutionRow Δ[1] (op ⦋0⦌)
    let ed := SSet.edgewiseResolutionRowExtraDegeneracy Δ[1] (op ⦋0⦌)
    (ed.s 0 ≫ R.left.δ 0) deltaOneIdentity = deltaOneIdentity := by
  exact ConcreteCategory.congr_hom
    ((SSet.edgewiseResolutionRowExtraDegeneracy Δ[1]
      (op ⦋0⦌)).s_comp_δ₀ 0) deltaOneIdentity

example :
    let R := SSet.edgewiseResolutionRow Δ[1] (op ⦋0⦌)
    let ed := SSet.edgewiseResolutionRowExtraDegeneracy Δ[1] (op ⦋0⦌)
    (ed.s 0 ≫ R.left.δ (Fin.last 1)) deltaOneIdentity ≠
      deltaOneIdentity := by
  dsimp
  intro hterminal
  let R := SSet.edgewiseResolutionRow Δ[1] (op ⦋0⦌)
  let ed := SSet.edgewiseResolutionRowExtraDegeneracy Δ[1] (op ⦋0⦌)
  have hspecial := ConcreteCategory.congr_hom ed.s₀_comp_δ₁ deltaOneIdentity
  have hprojection :
      (R.hom.app (op ⦋0⦌) ≫ ed.s') deltaOneIdentity = deltaOneIdentity :=
    hspecial.symm.trans hterminal
  change
    (Δ[1].map (AugmentedSimplexCategory.inr' ⦋0⦌ ⦋0⦌).op ≫
      Δ[1].map (SSet.edgewiseBoundarySection 0).op) deltaOneIdentity =
        deltaOneIdentity at hprojection
  rw [← Δ[1].map_comp] at hprojection
  change SSet.stdSimplex.objEquiv.symm
      (SSet.edgewiseBoundarySection 0 ≫
        AugmentedSimplexCategory.inr' ⦋0⦌ ⦋0⦌) =
    SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌) at hprojection
  exact (by decide :
    SSet.edgewiseBoundarySection 0 ≫
        AugmentedSimplexCategory.inr' ⦋0⦌ ⦋0⦌ ≠ 𝟙 ⦋1⦌)
      (SSet.stdSimplex.objEquiv.symm.injective hprojection)

-- Universe-polymorphic consumers.
noncomputable example (X : SSet.{0}) :
    SimplicialObject.Augmented SSet.{0} := SSet.edgewiseResolution X

noncomputable example (X : SSet.{1}) :
    SimplicialObject.Augmented SSet.{1} := SSet.edgewiseResolution X

noncomputable example (X : SSet.{1}) :
    SimplicialObject.Augmented (Type 1) :=
  SSet.edgewiseResolutionRow X (op ⦋2⦌)

-- The foundational leaf intentionally exposes no global contraction or
-- realization/weak-equivalence conclusion.

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.edgewiseResolutionExtraDegeneracy

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.edgewiseResolutionRightExtraDegeneracy

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.esdComparison_mem_realizationWeakEquivalences

#print axioms SSet.edgewiseResolution
#print axioms SSet.edgewiseResolutionDiagonalIso
#print axioms SSet.edgewiseResolution_diagonal_augmentation
#print axioms SSet.edgewiseResolutionRow
#print axioms SSet.edgewiseResolutionRowExtraDegeneracy

end MathlibExtTest.AlgebraicTopology.SimplicialSet.EdgewiseResolutionTests
