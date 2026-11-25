/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.DegreeAdjoint
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Adjoint Chevalley–Eilenberg coinvariant complexes

The coinvariant complex is the cokernel of the adjoint scalar-action chain
map. In each degree it is the exterior power modulo the span of adjoint
actions. Negating the action gives the same relation span and hence the same
quotient and projection kernel.

The acting scalar Lie algebra lies in the ring universe. The Lie algebra on
which it acts has an independent carrier universe.
-/

@[expose] public section

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]
variable {S : Type u} [LieRing S] [LieAlgebra R S] (ι : S →ₗ⁅R⁆ L)




/-- The span of left adjoint actions in one exterior degree. -/
def adjointDegreeSpan (n : ℕ) : Submodule R (⋀[R]^n L) :=
  Submodule.span R {y | ∃ (s : S) (a : ⋀[R]^n L), y = degreeAdjointAction R L n (ι s) a}

/-- The span of the right-adjoint actions. -/
def rightAdjointDegreeSpan (n : ℕ) : Submodule R (⋀[R]^n L) :=
  Submodule.span R {y | ∃ (s : S) (a : ⋀[R]^n L), y = rightDegreeAdjointAction R L ι n s a}

/-- Negating the native left action preserves exactly the coinvariant span. -/
theorem adjointDegreeSpan_eq_right (n : ℕ) :
    adjointDegreeSpan R L ι n = rightAdjointDegreeSpan R L ι n := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨s, a, rfl⟩
    have h : rightDegreeAdjointAction R L ι n s a ∈ rightAdjointDegreeSpan R L ι n :=
      Submodule.subset_span ⟨s, a, rfl⟩
    have he : degreeAdjointAction R L n (ι s) a = -rightDegreeAdjointAction R L ι n s a := by
      change degreeAdjointAction R L n (ι s) a = -(-(degreeAdjointAction R L n (ι s) a))
      exact (neg_neg _).symm
    rw [he]
    exact Submodule.neg_mem _ h
  · apply Submodule.span_le.mpr
    rintro _ ⟨s, a, rfl⟩
    change -degreeAdjointAction R L n (ι s) a ∈ adjointDegreeSpan R L ι n
    exact Submodule.neg_mem _ (Submodule.subset_span ⟨s, a, rfl⟩)

/-- The bilinear scalar action, descended through native tensor product. -/
def adjointActionLinear (ι : S →ₗ⁅R⁆ L) (n : ℕ) : (S ⊗[R] (⋀[R]^n L)) →ₗ[R] (⋀[R]^n L) :=
  TensorProduct.lift ((degreeAdjointAction R L n).comp ι).toLinearMap

@[simp]
theorem adjointActionLinear_tmul (n : ℕ) (s : S) (a : ⋀[R]^n L) :
    adjointActionLinear R L ι n (s ⊗ₜ[R] a) = degreeAdjointAction R L n (ι s) a := rfl

/-- The tensor action has exactly the action span as its range. -/
theorem adjointActionLinear_range (n : ℕ) :
    LinearMap.range (adjointActionLinear R L ι n) = adjointDegreeSpan R L ι n := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul s a => rw [adjointActionLinear_tmul]; exact Submodule.subset_span ⟨s, a, rfl⟩
    | add t t' ht ht' => rw [map_add]; exact Submodule.add_mem _ ht ht'
  · apply Submodule.span_le.mpr
    rintro _ ⟨s, a, rfl⟩
    exact ⟨s ⊗ₜ[R] a, adjointActionLinear_tmul R L ι n s a⟩

/-- The constant-scalar tensor of CE chain degrees. -/
def adjointActionComplex : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (S ⊗[R] (⋀[R]^n L)))
    (fun n => ModuleCat.ofHom ((differential R L n).lTensor S))
    (fun n => by
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro s a
      change s ⊗ₜ[R] (differential R L n (differential R L (n + 1) a)) = 0
      have h := LinearMap.congr_fun (differential_comp_differential R L n) a
      change differential R L n (differential R L (n + 1) a) = 0 at h
      rw [h, TensorProduct.tmul_zero])

@[simp]
theorem adjointActionComplex_d_succ (n : ℕ) :
    (adjointActionComplex R L (S := S)).d (n + 1) n =
      ModuleCat.ofHom ((differential R L n).lTensor S) := by
  simp only [adjointActionComplex, ChainComplex.of_d]

/-- The adjoint tensor action is a native chain map. -/
def adjointActionChainMap : adjointActionComplex R L (S := S) ⟶ ((canonicalChainData R L).complex) :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (adjointActionLinear R L ι n))
    (fun n => by
      have hD : ((canonicalChainData R L).complex).d (n + 1) n =
          ModuleCat.ofHom (differential R L n) := by
        rw [ChainData.complex_d_succ]
        rfl
      rw [adjointActionComplex_d_succ, hD]
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro s a
      change differential R L n (degreeAdjointAction R L (n + 1) (ι s) a) =
        degreeAdjointAction R L n (ι s) (differential R L n a)
      exact LinearMap.congr_fun (differential_degreeAdjointAction R L n (ι s)) a)

@[simp]
theorem adjointActionChainMap_f (n : ℕ) :
    (adjointActionChainMap R L ι).f n = ModuleCat.ofHom (adjointActionLinear R L ι n) := rfl

/-- The native CE coinvariant complex is the cokernel of the scalar chain action. -/
def adjointCoinvariantComplex : ChainComplex (ModuleCat.{max u v} R) ℕ := cokernel (adjointActionChainMap R L ι)

/-- The canonical projection to CE coinvariants. -/
def adjointCoinvariantProjection : ((canonicalChainData R L).complex) ⟶ adjointCoinvariantComplex R L ι :=
  cokernel.π (adjointActionChainMap R L ι)

instance adjointCoinvariantProjection_epi : Epi (adjointCoinvariantProjection R L ι) := by
  unfold adjointCoinvariantProjection
  exact Cofork.IsColimit.epi
    (s := Cofork.ofπ (cokernel.π (adjointActionChainMap R L ι))
      ((cokernel.condition (adjointActionChainMap R L ι)).trans zero_comp.symm))
    (cokernelIsCokernel (adjointActionChainMap R L ι))

instance adjointCoinvariantProjection_f_epi (n : ℕ) :
    Epi ((adjointCoinvariantProjection R L ι).f n) := by
  change Epi ((HomologicalComplex.eval (ModuleCat.{max u v} R) (ComplexShape.down ℕ) n).map
    (cokernel.π (adjointActionChainMap R L ι)))
  infer_instance

/-- The exterior-power action quotient in each degree. -/
abbrev adjointCoinvariantModule (n : ℕ) := (⋀[R]^n L) ⧸ adjointDegreeSpan R L ι n

/-- Native cokernel evaluation identifies the coinvariant degree with its quotient. -/
def adjointCoinvariantCoordinateIso (n : ℕ) :
    (adjointCoinvariantComplex R L ι).X n ≅ ModuleCat.of R (adjointCoinvariantModule R L ι n) :=
  PreservesCokernel.iso (HomologicalComplex.eval (ModuleCat.{max u v} R) (ComplexShape.down ℕ) n)
      (adjointActionChainMap R L ι) ≪≫
    ModuleCat.cokernelIsoRangeQuotient ((adjointActionChainMap R L ι).f n) ≪≫
      (Submodule.quotEquivOfEq _ _ (adjointActionLinear_range R L ι n)).toModuleIso

/-- The native projection is the quotient projection in the coordinates. -/
theorem adjointCoinvariantProjection_coordinates (n : ℕ) :
    (adjointCoinvariantProjection R L ι).f n ≫ (adjointCoinvariantCoordinateIso R L ι n).hom =
      ModuleCat.ofHom (adjointDegreeSpan R L ι n).mkQ := by
  let F := HomologicalComplex.eval (ModuleCat.{max u v} R) (ComplexShape.down ℕ) n
  let a := adjointActionChainMap R L ι
  let e₁ := PreservesCokernel.iso F a
  let e₂ := ModuleCat.cokernelIsoRangeQuotient (a.f n)
  let e₃ := (Submodule.quotEquivOfEq _ _ (adjointActionLinear_range R L ι n)).toModuleIso
  have hE : (adjointCoinvariantCoordinateIso R L ι n).hom = e₁.hom ≫ e₂.hom ≫ e₃.hom := rfl
  have hP : (adjointCoinvariantProjection R L ι).f n ≫ e₁.hom = cokernel.π (a.f n) :=
    PreservesCokernel.π_iso_hom F a
  have hQ : cokernel.π (a.f n) ≫ e₂.hom = ModuleCat.ofHom ((a.f n).hom.range.mkQ) :=
    ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom (a.f n)
  have hLast : ModuleCat.ofHom ((a.f n).hom.range.mkQ) ≫ e₃.hom =
      (ModuleCat.ofHom (adjointDegreeSpan R L ι n).mkQ :
        ModuleCat.of R (⋀[R]^n L) ⟶ ModuleCat.of R (adjointCoinvariantModule R L ι n)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  have h₁ := congrArg (fun z => (adjointCoinvariantProjection R L ι).f n ≫ z) hE
  have h₂ := (Category.assoc ((adjointCoinvariantProjection R L ι).f n)
    e₁.hom (e₂.hom ≫ e₃.hom)).symm
  have h₃ := congrArg (fun z => z ≫ e₂.hom ≫ e₃.hom) hP
  have h₄ := (Category.assoc (cokernel.π (a.f n)) e₂.hom e₃.hom).symm
  have h₅ := congrArg (fun z => z ≫ e₃.hom) hQ
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans hLast))))

/-- Every component projection has the exact action-span kernel. -/
theorem adjointCoinvariantProjection_ker (n : ℕ) :
    LinearMap.ker ((adjointCoinvariantProjection R L ι).f n).hom = adjointDegreeSpan R L ι n := by
  ext a
  rw [LinearMap.mem_ker]
  have h := congrArg (fun f => f.hom a) (adjointCoinvariantProjection_coordinates R L ι n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at h
  constructor
  · intro ha
    rw [ha, map_zero] at h
    exact (Submodule.Quotient.mk_eq_zero _).mp h.symm
  · intro ha
    apply (adjointCoinvariantCoordinateIso R L ι n).toLinearEquiv.injective
    change (adjointCoinvariantCoordinateIso R L ι n).hom.hom
      (((adjointCoinvariantProjection R L ι).f n).hom a) =
      (adjointCoinvariantCoordinateIso R L ι n).hom.hom 0
    have hQ : (ModuleCat.ofHom (adjointDegreeSpan R L ι n).mkQ).hom a = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ha
    exact h.trans (hQ.trans (adjointCoinvariantCoordinateIso R L ι n).hom.hom.map_zero.symm)

/-- The projection kernel is the span of right-adjoint actions. -/
theorem adjointCoinvariantProjection_ker_right (n : ℕ) :
    LinearMap.ker ((adjointCoinvariantProjection R L ι).f n).hom =
      Submodule.span R {y | ∃ (s : S) (a : ⋀[R]^n L), y = rightDegreeAdjointAction R L ι n s a} := by
  rw [adjointCoinvariantProjection_ker, adjointDegreeSpan_eq_right]
  rfl

/-- The scalar-action pure inclusion is a native chain map. -/
def adjointScalarChainMap (s : S) : ((canonicalChainData R L).complex) ⟶ adjointActionComplex R L (S := S) :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (TensorProduct.mk R S (⋀[R]^n L) s))
    (fun n => by
      have hD : ((canonicalChainData R L).complex).d (n + 1) n =
          ModuleCat.ofHom (differential R L n) := by
        rw [ChainData.complex_d_succ]
        rfl
      rw [hD, adjointActionComplex_d_succ]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      change s ⊗ₜ[R] differential R L n a = s ⊗ₜ[R] differential R L n a
      rfl)

/-- Each degreewise adjoint chain map factors through the scalar tensor action. -/
theorem adjointScalarChainMap_action (s : S) :
    adjointScalarChainMap R L s ≫ adjointActionChainMap R L ι = degreeAdjointChainMap R L (ι s) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact adjointActionLinear_tmul R L ι n s a

/-- Every adjoint chain action vanishes after the coinvariant projection. -/
theorem degreeAdjointChainMap_projection (s : S) :
    degreeAdjointChainMap R L (ι s) ≫ adjointCoinvariantProjection R L ι = 0 := by
  rw [← adjointScalarChainMap_action R L ι s, Category.assoc]
  unfold adjointCoinvariantProjection
  exact (congrArg (fun z => adjointScalarChainMap R L s ≫ z)
    (cokernel.condition (adjointActionChainMap R L ι))).trans comp_zero

end ChevalleyEilenberg
