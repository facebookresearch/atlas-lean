/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.ExteriorPower.ProductFiltration.AssociatedGradedMap

/-!
# Transported exterior filtrations and triangular operators

Fix a commutative ring R, R-modules M and N, a degree m and linear coordinates e : X ≃ₗ[R]
⋀[R]^m(M × N). The filtration on X is the inverse image of the mixed-weight filtration: in
stage q, every coordinate with fewer than q factors from M is zero. The stage equivalence
induced by e identifies adjacent-stage quotients with the corresponding exterior-product
grades. For q ≤ m, this quotient is ⋀[R]^q M ⊗[R] ⋀[R]^(m−q) N.

Clipping coordinates of first weight below q gives a linear retraction X → F_X^q. For a
first-summand-preserving linear map f : M × N → M' × N' and target coordinates e', the
operator e'⁻¹ ∘ ⋀^m f ∘ e preserves the stages. Its map on the q-th grade is ⋀^q f.first ⊗
⋀^(m−q) f.relative, where f.relative is the induced map from N to N'. The modules and
coordinate carriers may have different universes.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w x v' w' x'

namespace exteriorPower.ProductFiltration.CoordinateTransport

variable (R : Type u) [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M]
  (N : Type w) [AddCommGroup N] [Module R N]
  {X : Type x} [AddCommGroup X] [Module R X]
  (m : ℕ) (e : X ≃ₗ[R] (⋀[R]^m (M × N)))

-- Explicitly select the canonical native exterior and subgroup data.
local instance (Y : Type*) [AddCommGroup Y] [Module R Y] (d : ℕ) :
    AddCommGroup (⋀[R]^d Y) :=
  Submodule.addCommGroup (R := R) (M := ExteriorAlgebra R Y)
    (ExteriorAlgebra.exteriorPower R d Y)

local instance (A : Type*) [AddCommGroup A] [Module R A]
    (B : Type*) [AddCommGroup B] [Module R B] (d q : ℕ) :
    AddCommGroup (ProductFiltration.filtration R A B d q) :=
  Submodule.addCommGroup (R := R) (M := ⋀[R]^d (A × B))
    (ProductFiltration.filtration R A B d q)

def filtration (q : ℕ) : Submodule R X :=
  (ProductFiltration.filtration R M N m q).comap e.toLinearMap

local instance (q : ℕ) : AddCommGroup (filtration R M N m e q) :=
  Submodule.addCommGroup (R := R) (M := X) (filtration R M N m e q)

def stageEquiv (q : ℕ) :
    filtration R M N m e q ≃ₗ[R] ProductFiltration.filtration R M N m q :=
  e.ofSubmodule' (ProductFiltration.filtration R M N m q)

def nextStage (q : ℕ) : Submodule R (filtration R M N m e q) :=
  (filtration R M N m e (q + 1)).comap (filtration R M N m e q).subtype

theorem nextStage_image (q : ℕ) :
    (nextStage R M N m e q).map (stageEquiv R M N m e q).toLinearMap =
      ProductFiltration.nextStage R M N m q := by
  apply le_antisymm
  · rintro y ⟨z, hz, rfl⟩
    exact hz
  · intro y hy
    refine ⟨(stageEquiv R M N m e q).symm y, ?_, LinearEquiv.apply_symm_apply _ y⟩
    change e (e.symm y.val) ∈ ProductFiltration.filtration R M N m (q + 1)
    rw [LinearEquiv.apply_symm_apply]
    exact hy

abbrev associatedGraded (q : ℕ) := filtration R M N m e q ⧸ nextStage R M N m e q

def quotientEquiv (q : ℕ) :
    associatedGraded R M N m e q ≃ₗ[R] ProductFiltration.associatedGraded R M N m q :=
  by
    let P : Submodule R (filtration R M N m e q) := nextStage R M N m e q
    let Q : Submodule R (ProductFiltration.filtration R M N m q) :=
      ProductFiltration.nextStage R M N m q
    let E : filtration R M N m e q ≃ₗ[R] ProductFiltration.filtration R M N m q :=
      stageEquiv R M N m e q
    have hE : P.map E.toLinearMap = Q := nextStage_image R M N m e q
    let hquot :
        (filtration R M N m e q ⧸ P) ≃ₗ[R]
          (ProductFiltration.filtration R M N m q ⧸ Q) :=
      Submodule.Quotient.equiv (R := R) (R₂ := R)
        (σ₁₂ := RingHom.id R) (σ₂₁ := RingHom.id R)
        (M := filtration R M N m e q)
        (N := ProductFiltration.filtration R M N m q) P Q E hE
    exact hquot

def coordinateEquiv (q : ℕ) (hq : q ≤ m) :
    associatedGraded R M N m e q ≃ₗ[R] (⋀[R]^q M) ⊗[R] (⋀[R]^(m - q) N) :=
  (quotientEquiv R M N m e q).trans (ProductFiltration.associatedGradedEquiv R M N m q hq)

theorem quotientEquiv_mk (q : ℕ) (z : filtration R M N m e q) :
    quotientEquiv R M N m e q (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (stageEquiv R M N m e q z) := rfl

private theorem coordinateEquiv_mk (q : ℕ) (hq : q ≤ m)
    (z : filtration R M N m e q) :
    coordinateEquiv R M N m e q hq
        (Submodule.Quotient.mk (p := nextStage R M N m e q) z) =
      ProductFiltration.associatedGradedEquiv R M N m q hq
        (Submodule.Quotient.mk (p := ProductFiltration.nextStage R M N m q)
          (stageEquiv R M N m e q z)) := by
  exact congrArg (fun y : ProductFiltration.associatedGraded R M N m q =>
    ProductFiltration.associatedGradedEquiv R M N m q hq y)
      (quotientEquiv_mk R M N m e q z)

/-- Let R be a commutative ring, M and N R-modules, m : ℕ, and e : X ≃ₗ[R] ⋀[R]^m (M × N) a linear
equivalence from an R-module X. For q : ℕ, let F_X^q be the inverse image under e of the
exterior-product filtration F_m^q, defined by vanishing coordinates with first weight below q.
The map retraction q : X →ₗ[R] F_X^q first applies e, discards those lower-weight coordinates,
and transports the resulting stage element back along the inverse stage equivalence. On the
inclusion F_X^q → X it is the identity. -/
def retraction (q : ℕ) : X →ₗ[R] filtration R M N m e q :=
  (stageEquiv R M N m e q).symm.toLinearMap.comp
    ((ProductFiltration.projectionToFiltration R M N m q).comp e.toLinearMap)

theorem retraction_subtype (q : ℕ) (z : filtration R M N m e q) :
    retraction R M N m e q z.val = z := by
  apply (stageEquiv R M N m e q).injective
  change stageEquiv R M N m e q
    ((stageEquiv R M N m e q).symm
      (ProductFiltration.projectionToFiltration R M N m q (e z.val))) =
    stageEquiv R M N m e q z
  rw [LinearEquiv.apply_symm_apply]
  exact ProductFiltration.projectionToFiltration_subtype R M N m q
    (stageEquiv R M N m e q z)

variable {R M N m}
  {M' : Type v'} [AddCommGroup M'] [Module R M']
  {N' : Type w'} [AddCommGroup N'] [Module R N']
  {X' : Type x'} [AddCommGroup X'] [Module R X']
  (e' : X' ≃ₗ[R] (⋀[R]^m (M' × N')))
  (f : FirstSummandMap (R := R) (M := M) (N := N) (M' := M') (N' := N'))

def operator : X →ₗ[R] X' :=
  e'.symm.toLinearMap.comp ((exteriorPower.map m f.map).comp e.toLinearMap)

def stageMap (q : ℕ) :
    filtration R M N m e q →ₗ[R] filtration R M' N' m e' q :=
  (stageEquiv R M' N' m e' q).symm.toLinearMap.comp
    ((f.stageMap m q).comp (stageEquiv R M N m e q).toLinearMap)

theorem stageMap_value (q : ℕ) (z : filtration R M N m e q) :
    (stageMap e e' f q z : X') = operator e e' f z.val := by
  change e'.symm (exteriorPower.map m f.map (e z.val)) = operator e e' f z.val
  rfl

theorem stageMap_coordinates (q : ℕ) (z : filtration R M N m e q) :
    stageEquiv R M' N' m e' q (stageMap e e' f q z) =
      f.stageMap m q (stageEquiv R M N m e q z) := by
  change stageEquiv R M' N' m e' q
    ((stageEquiv R M' N' m e' q).symm
      (f.stageMap m q (stageEquiv R M N m e q z))) =
    f.stageMap m q (stageEquiv R M N m e q z)
  exact (stageEquiv R M' N' m e' q).apply_symm_apply _

theorem stageMap_next (q : ℕ) :
    nextStage R M N m e q ≤ (nextStage R M' N' m e' q).comap (stageMap e e' f q) := by
  intro z hz
  change e' ((stageMap e e' f q z).val) ∈ ProductFiltration.filtration R M' N' m (q + 1)
  rw [stageMap_value]
  change e' (e'.symm (exteriorPower.map m f.map (e z.val))) ∈
    ProductFiltration.filtration R M' N' m (q + 1)
  rw [LinearEquiv.apply_symm_apply]
  exact f.map_mem_filtration m (q + 1) (e z.val) hz

def gradeMap (q : ℕ) :
    associatedGraded R M N m e q →ₗ[R] associatedGraded R M' N' m e' q :=
  (nextStage R M N m e q).mapQ (nextStage R M' N' m e' q)
    (stageMap e e' f q) (stageMap_next e e' f q)

theorem gradeMap_mk (q : ℕ) (z : filtration R M N m e q) :
    gradeMap e e' f q (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (stageMap e e' f q z) := by
  exact Submodule.mapQ_apply (R := R) (R₂ := R)
    (M := filtration R M N m e q) (M₂ := filtration R M' N' m e' q)
    (nextStage R M N m e q) (nextStage R M' N' m e' q)
    (stageMap e e' f q) (h := stageMap_next e e' f q) z

/-- Let R be a commutative ring, M and N R-modules, m : ℕ, and e : X ≃ₗ[R] ⋀[R]^m (M × N) a linear
equivalence from an R-module X. Let M', N' and X' be R-modules with coordinates e' : X' ≃ₗ[R]
⋀[R]^m (M' × N'). Let f : M × N →ₗ[R] M' × N' and f.first : M →ₗ[R] M' satisfy f ∘ inl = inl'
∘ f.first, and put f.relative = snd' ∘ f ∘ inr. For q ≤ m, the induced quotient map G_q of
e'⁻¹ ∘ ⋀^m f ∘ e satisfies E'_q(G_q(z)) = TensorProduct.map (⋀^q f.first) (⋀^(m−q) f.relative)
(E_q(z)) for every source grade class z. Here E_q and E'_q are the mixed-tensor coordinate
equivalences of the transported adjacent-stage quotients. -/
theorem coordinateEquiv_gradeMap (q : ℕ) (hq : q ≤ m)
    (z : associatedGraded R M N m e q) :
    coordinateEquiv R M' N' m e' q hq (gradeMap e e' f q z) =
      TensorProduct.map (exteriorPower.map q f.first) (exteriorPower.map (m - q) f.relative)
        (coordinateEquiv R M N m e q hq z) := by
  refine Submodule.Quotient.induction_on (nextStage R M N m e q) z (fun x => ?_)
  let oldx : ProductFiltration.associatedGraded R M N m q :=
    Submodule.Quotient.mk (p := ProductFiltration.nextStage R M N m q)
      (stageEquiv R M N m e q x)
  let tmap := TensorProduct.map (exteriorPower.map q f.first)
    (exteriorPower.map (m - q) f.relative)
  have hqmap :
      (Submodule.Quotient.mk (p := ProductFiltration.nextStage R M' N' m q)
        (stageEquiv R M' N' m e' q (stageMap e e' f q x)) :
          ProductFiltration.associatedGraded R M' N' m q) =
      f.gradeMap m q oldx :=
    (congrArg (fun y : ProductFiltration.filtration R M' N' m q =>
      (Submodule.Quotient.mk (p := ProductFiltration.nextStage R M' N' m q) y :
        ProductFiltration.associatedGraded R M' N' m q))
          (stageMap_coordinates e e' f q x)).trans
      (f.gradeMap_mk m q (stageEquiv R M N m e q x)).symm
  have h₁ := congrArg (fun y : associatedGraded R M' N' m e' q =>
    coordinateEquiv R M' N' m e' q hq y) (gradeMap_mk e e' f q x)
  have h₂ := coordinateEquiv_mk R M' N' m e' q hq (stageMap e e' f q x)
  have h₃ := congrArg (fun y : ProductFiltration.associatedGraded R M' N' m q =>
    ProductFiltration.associatedGradedEquiv R M' N' m q hq y) hqmap
  have h₄ := f.associatedGradedEquiv_gradeMap m q hq oldx
  have h₅ := congrArg tmap (coordinateEquiv_mk R M N m e q hq x).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

end exteriorPower.ProductFiltration.CoordinateTransport

end
