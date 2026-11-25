/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.CountableComultiplicationClosure
public import MathlibExt.Algebra.Homology.ModelCategory.IntTensorExact
public import MathlibExt.CategoryTheory.Monoidal.ComonObjOfMono
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# DG subcomonoid closures over a field

An arbitrary homogeneous seed set determines a subcomonoid closed under
the original differential and comultiplication. The original tensor factors
place the comultiplication in the image of the tensor square of the
subcomplex inclusion. Countable seeds give a countable homogeneous basis.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CochainComplex

universe u
variable {R : Type u} [Field R]
variable [∀ X Y : GradedObject ℤ (ModuleCat.{u} R), GradedObject.HasTensor X Y]

variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

/-- An actual pure homogeneous tensor maps to the pure tensor of its actual factor images. -/
lemma homogeneousTensorTerm_map (f : K ⟶ L) {n : ℤ} (t : HomogeneousTensorTerm K n) :
    ((HomologicalComplex.tensorHom f f).f n).hom (HomogeneousTensorTerm.value K t) =
      HomogeneousTensorTerm.value L
        ⟨t.leftDegree, (f.f t.leftDegree).hom t.left, (f.f (n - t.leftDegree)).hom t.right⟩ := by
  change (HomologicalComplex.ιTensorObj K K t.leftDegree (n - t.leftDegree) n (by omega) ≫
    (HomologicalComplex.tensorHom f f).f n).hom (TensorProduct.tmul R t.left t.right) = _
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp [HomogeneousTensorTerm.value]

variable [∀ X : ModuleCat.{u} R,
  PreservesColimit (Functor.empty.{0} (ModuleCat.{u} R)) ((curriedTensor (ModuleCat.{u} R)).obj X)]
variable [∀ X : ModuleCat.{u} R,
  PreservesColimit (Functor.empty.{0} (ModuleCat.{u} R))
    ((curriedTensor (ModuleCat.{u} R)).flip.obj X)]
variable [∀ W X Y Z : GradedObject ℤ (ModuleCat.{u} R), GradedObject.HasTensor₄ObjExt W X Y Z]
variable [∀ X Y Z : GradedObject ℤ (ModuleCat.{u} R), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
variable [∀ X Y Z : GradedObject ℤ (ModuleCat.{u} R), GradedObject.HasGoodTensorTensor₂₃ X Y Z]

local instance : ∀ M : ModuleCat.{u} R, Projective M := fun _ => inferInstance
variable (C : CochainComplex (ModuleCat.{u} R) ℤ) [ComonObj C]
  (s : Set (HomogeneousElement C))

/-- The honest DG subcomplex closed under the actual original comultiplication. -/
abbrev coalgebraClosureSubcomplex : HomogeneousSubcomplex C :=
  dgCoalgebraClosureSubcomplex C (ComonObj.comul (X := C)) s

/-- Its original integer-graded carrier. -/
abbrev coalgebraClosureCarrier := (coalgebraClosureSubcomplex C s).complex

/-- The actual original subtype chain map. -/
abbrev coalgebraClosureInclusion : coalgebraClosureCarrier C s ⟶ C :=
  (coalgebraClosureSubcomplex C s).inclusion

/-- The original inclusion on the original full tensor square. -/
abbrev coalgebraClosureTensorInclusion :
    HomologicalComplex.tensorObj (coalgebraClosureCarrier C s) (coalgebraClosureCarrier C s) ⟶
      HomologicalComplex.tensorObj C C :=
  HomologicalComplex.tensorHom (coalgebraClosureInclusion C s) (coalgebraClosureInclusion C s)

instance coalgebraClosureTensorInclusion_mono : Mono (coalgebraClosureTensorInclusion C s) :=
  tensorHom_mono_of_allProjective _ _

/-- The chosen original finite factors supply an actual preimage of every chosen pure tensor. -/
lemma coalgebraClosureTerm_mem_tensorRange {n : ℤ} {x : C.X n}
    (hx : (⟨n, x⟩ : HomogeneousElement C) ∈ dgCoalgebraClosure C ComonObj.comul s)
    (t : HomogeneousTensorTerm C n)
    (ht : t ∈ finiteHomogeneousTensorTerms C (((ComonObj.comul (X := C)).f n).hom x)) :
    HomogeneousTensorTerm.value C t ∈ LinearMap.range
      ((coalgebraClosureTensorInclusion C s).f n).hom := by
  obtain ⟨hL, hR⟩ := dgCoalgebraClosure_factors_mem C ComonObj.comul hx t ht
  let t' : HomogeneousTensorTerm (coalgebraClosureCarrier C s) n :=
    ⟨t.leftDegree, ⟨t.left, Submodule.subset_span hL⟩, ⟨t.right, Submodule.subset_span hR⟩⟩
  refine ⟨HomogeneousTensorTerm.value (coalgebraClosureCarrier C s) t', ?_⟩
  exact homogeneousTensorTerm_map (coalgebraClosureInclusion C s) t'

/-- The whole span maps under the ORIGINAL comultiplication into the ORIGINAL tensor-square
image. -/
lemma coalgebraClosureComul_mem_tensorRange (n : ℤ) (x : (coalgebraClosureCarrier C s).X n) :
    ((coalgebraClosureInclusion C s ≫ ComonObj.comul).f n).hom x ∈
      LinearMap.range ((coalgebraClosureTensorInclusion C s).f n).hom := by
  let T := LinearMap.range ((coalgebraClosureTensorInclusion C s).f n).hom
  have h : dgCoalgebraDegreeSpan C ComonObj.comul s n ≤
      T.comap ((ComonObj.comul (X := C)).f n).hom := by
    apply Submodule.span_le.mpr
    intro y hy
    have hTerms : Submodule.span R ((HomogeneousTensorTerm.value C) ''
        (finiteHomogeneousTensorTerms C
          (((ComonObj.comul (X := C)).f n).hom y) : Set (HomogeneousTensorTerm C n))) ≤ T := by
      apply Submodule.span_le.mpr
      rintro z ⟨t, ht, rfl⟩
      exact coalgebraClosureTerm_mem_tensorRange C s hy t ht
    exact hTerms (finiteHomogeneousTensorTerms_spec C (((ComonObj.comul (X := C)).f n).hom y))
  exact h x.property

/-- Honest DG restriction of the ORIGINAL comultiplication, using the original tensor-square
mono inverse. -/
def coalgebraClosureComul : coalgebraClosureCarrier C s ⟶
    HomologicalComplex.tensorObj (coalgebraClosureCarrier C s) (coalgebraClosureCarrier C s) :=
  liftThroughMono (coalgebraClosureTensorInclusion C s)
    (coalgebraClosureInclusion C s ≫ ComonObj.comul) (coalgebraClosureComul_mem_tensorRange C s)

lemma coalgebraClosureComul_fac :
    coalgebraClosureComul C s ≫ coalgebraClosureTensorInclusion C s =
      coalgebraClosureInclusion C s ≫ ComonObj.comul :=
  liftThroughMono_fac _ _ _

local instance coalgebraClosureUnitLeft_mono :
    Mono (𝟙 (𝟙_ _) ⊗ₘ coalgebraClosureInclusion C s) :=
  tensorHom_mono_of_allProjective _ _

local instance coalgebraClosureUnitRight_mono :
    Mono (coalgebraClosureInclusion C s ⊗ₘ 𝟙 (𝟙_ _)) :=
  tensorHom_mono_of_allProjective _ _

local instance coalgebraClosureSquare_mono :
    Mono (coalgebraClosureInclusion C s ⊗ₘ coalgebraClosureInclusion C s) :=
  coalgebraClosureTensorInclusion_mono C s

local instance coalgebraClosureTriple_mono :
    Mono (coalgebraClosureInclusion C s ⊗ₘ
      (coalgebraClosureInclusion C s ⊗ₘ coalgebraClosureInclusion C s)) :=
  tensorHom_mono_of_allProjective _ _

/-- Actual original comonoid structure, with every law derived from the original target and
tensor monos. -/
@[instance_reducible]
def coalgebraClosureComonObj : ComonObj (coalgebraClosureCarrier C s) :=
  ComonObj.ofTensorStableMono (coalgebraClosureInclusion C s)
    (coalgebraClosureComul C s) (coalgebraClosureComul_fac C s)

lemma coalgebraClosureInclusion_isComonHom :
    letI := coalgebraClosureComonObj C s
    IsComonHom (coalgebraClosureInclusion C s) :=
  ComonObj.ofTensorStableMono_isComonHom _ _ _

/-- The bundled DG subcomonoid closure of the given homogeneous seed set. -/
def coalgebraClosureComon : CategoryTheory.Comon (CochainComplex (ModuleCat.{u} R) ℤ) where
  X := coalgebraClosureCarrier C s
  comon := coalgebraClosureComonObj C s

/-- Its honest bundled original comonoid monomorphism. -/
def coalgebraClosureComonInclusion : coalgebraClosureComon C s ⟶ Comon.mk C where
  hom := coalgebraClosureInclusion C s
  isComonHom_hom := coalgebraClosureInclusion_isComonHom C s

lemma coalgebraClosureComonInclusion_carrier : (coalgebraClosureComonInclusion C s).hom =
    coalgebraClosureInclusion C s := rfl

/-- A countable seed set gives a homogeneous basis with countable indices in all degrees. -/
def countableCoalgebraBasis (hs : s.Countable) :
    CountableHomogeneousBasis (coalgebraClosureCarrier C s) :=
  dgCoalgebraClosureCountableHomogeneousBasis C ComonObj.comul s hs

end CochainComplex
