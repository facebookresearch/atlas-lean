/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialResolutionContraction
public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialCotangentResolutionFunctor
public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialGroupKan
public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialObjectHomotopyRealization
public import MathlibExt.AlgebraicTopology.SimplicialSet.FibrationToConstant
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup

/-!
# Native asphericity of the canonical polynomial resolution

Let k be a commutative ring. The additive-group structure of a simplicial commutative k-algebra
makes its underlying simplicial set Kan. For the canonical augmented polynomial resolution of a
k-algebra A, the extra degeneracy contracts the augmentation after realization, and the map to
constant A is a fibration.

Consequently the canonical augmentation is a trivial fibration of simplicial sets. Polynomial
presentations in every degree then give a canonical object of the full category of polynomial
cotangent resolutions of A.

The ground-ring universe u and algebra carrier parameter v are independent; the diagrams and
underlying sets use the stable carrier max(u,v).

References: Stacks Project, Sections 92.3–92.4; Weibel, 8.6.16.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

universe u v

namespace CommAlgCat

variable (k : Type u) [CommRing k]

/-- For a commutative ring k, send a commutative k-algebra to its additive group, regarded as an
object of GrpCat. Algebra maps induce the homomorphisms of these groups. -/
def additiveGroupFunctor : CommAlgCat.{max u v} k ⥤ GrpCat.{max u v} :=
  forget₂ (CommAlgCat.{max u v} k) CommRingCat.{max u v} ⋙
    forget₂ CommRingCat.{max u v} RingCat.{max u v} ⋙
      forget₂ RingCat.{max u v} AddCommGrpCat.{max u v} ⋙
        AddCommGrpCat.toCommGrp ⋙ forget₂ CommGrpCat.{max u v} GrpCat.{max u v}

/-- For a commutative ring k, forgetting the additive-group functor further to sets is naturally
isomorphic to forgetting the algebra directly to its underlying set. -/
def additiveGroupForgetIso :
    additiveGroupFunctor.{u, v} k ⋙ forget GrpCat.{max u v} ≅
      forget (CommAlgCat.{max u v} k) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro P Q f
    change (forget (CommAlgCat.{max u v} k)).map f ≫ 𝟙 _ =
      𝟙 _ ≫ (forget (CommAlgCat.{max u v} k)).map f
    rw [Category.comp_id, Category.id_comp])

/-- For a commutative ring k, every simplicial commutative k-algebra X has a Kan underlying
simplicial set. The horn fillers come from the simplicial additive-group structure. -/
theorem underlying_simplicial_isKan (X : SimplicialObject (CommAlgCat.{max u v} k)) :
    SSet.KanComplex (X ⋙ forget (CommAlgCat.{max u v} k)) := by
  let G := X ⋙ additiveGroupFunctor k
  have hG : SSet.KanComplex (SSet.SimplicialGroupHorn.underlying G) :=
    SSet.SimplicialGroupHorn.underlying_isKan G
  change SSet.KanComplex (X ⋙ forget (CommAlgCat.{max u v} k)) at hG
  exact hG

variable (A : CommAlgCat.{max u v} k)

/-- For a commutative ring k and a commutative k-algebra A, the canonical polynomial augmentation to
the constant simplicial set A is a realization weak equivalence, induced by its extra-degeneracy
contraction. -/
theorem polynomialResolutionUnderlying_realizationWeak :
    SSet.realizationWeakEquivalences (polynomialResolutionUnderlying k A).hom :=
  (polynomialResolutionExtraDegeneracy k A).hom_mem_realizationWeakEquivalences

/-- For a commutative ring k and a commutative k-algebra A, the simplicial set underlying its
canonical polynomial resolution is Kan. -/
theorem polynomialResolutionUnderlying_isKan :
    SSet.KanComplex (polynomialResolutionUnderlying k A).left :=
  underlying_simplicial_isKan k (polynomialResolution k A).left

/-- For a commutative ring k and a commutative k-algebra A, the canonical polynomial augmentation to
the constant simplicial set A is a fibration in the Quillen model structure. -/
theorem polynomialResolutionUnderlying_fibration :
    Fibration (polynomialResolutionUnderlying k A).hom := by
  letI : SSet.KanComplex (polynomialResolutionUnderlying k A).left :=
    polynomialResolutionUnderlying_isKan k A
  letI : SSet.KanComplex ((𝟭 SSet.{max u v}).obj (polynomialResolutionUnderlying k A).left) :=
    polynomialResolutionUnderlying_isKan k A
  exact SSet.fibration_to_constant (polynomialResolutionUnderlying k A).hom

/-- For a commutative ring k and a commutative k-algebra A, the canonical polynomial augmentation is
both a fibration and a realization weak equivalence, hence a trivial fibration of simplicial
sets. -/
theorem polynomialResolutionUnderlying_trivialFibration :
    trivialFibrations SSet.{max u v} (polynomialResolutionUnderlying k A).hom := by
  letI : Fibration (polynomialResolutionUnderlying k A).hom :=
    polynomialResolutionUnderlying_fibration k A
  letI : WeakEquivalence (polynomialResolutionUnderlying k A).hom :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr
      (polynomialResolutionUnderlying_realizationWeak k A)
  exact (mem_trivialFibrations_iff _).mpr ⟨inferInstance, inferInstance⟩

/-- For a commutative ring k and a commutative k-algebra A, the canonical augmented polynomial
algebra satisfies the cotangent-resolution condition: its underlying simplicial-set augmentation
to constant A is a trivial fibration. -/
theorem polynomialResolutionOver_nativeCondition :
    polynomialCotangentResolutionCondition k A
      ((polynomialResolutionOverFunctor k A).obj (Over.mk (𝟙 A))) := by
  change trivialFibrations SSet.{max u v} (polynomialResolutionUnderlying k A).hom
  exact polynomialResolutionUnderlying_trivialFibration k A

/-- For a commutative ring k and a commutative k-algebra A, every natural-number degree n of the
canonical polynomial resolution is isomorphic to a polynomial k-algebra k[σ] for a variable set
σ in the stable algebra carrier universe max(u,v). -/
theorem polynomialResolutionOver_polynomialLevels (n : ℕ) :
    ∃ σ : Type (max u v), Nonempty ((free.{u, v} k).obj σ ≅
      (((polynomialResolutionOverFunctor k A).obj (Over.mk (𝟙 A))).left.obj (op ⦋n⦌))) :=
  ⟨((polynomialPower.{u, v} k n).obj A : Type (max u v)),
    ⟨(polynomialResolutionObjIso.{u, v} k A n).symm⟩⟩

/-- For a commutative ring k and a commutative k-algebra A, its canonical augmented polynomial
diagram is an object of the full category of polynomial cotangent resolutions: every level is
polynomial and the underlying augmentation is a trivial fibration. -/
def canonicalPolynomialCotangentResolution : PolynomialCotangentResolutions k A :=
  ⟨(polynomialResolutionOverFunctor k A).obj (Over.mk (𝟙 A)),
    polynomialResolutionOver_polynomialLevels k A, polynomialResolutionOver_nativeCondition k A⟩

end CommAlgCat

end
