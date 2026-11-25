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

public import MathlibExt.Algebra.Homology.HomologyCoalgebra.Primitives
public import MathlibExt.Algebra.Homology.HomologyCoalgebra.NativeUnitComparison
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoalgebraNaturality
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.PrimitiveFree
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.HomologyDiagonal

/-!
# Chevalley–Eilenberg homology coalgebras

For a commutative ring and a Lie algebra in a common carrier universe, the chain coproduct
induces a graded map to homology of the tensor square. Over a field, the Künneth isomorphism
gives a coaugmented graded cocommutative coalgebra on Chevalley–Eilenberg homology.

The primitive chain complex has a canonical homology comparison to the primitive part of
homology. With a free Lie carrier, its homology in degree one identifies with that carrier.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ComonObj

namespace ChevalleyEilenberg.HomologyCoalgebra

variable (R : Type u) [CommRing R]
variable (L : Type u) [LieRing L] [LieAlgebra R L]


namespace UnitComparison


/-- The constructed CE coalgebra with its fixed common-universe lifted scalar-unit structure. -/
def sourceCoalgebra : Comon (HomologicalComplex.HomologyCoalgebra.LiftedUnitChain R) :=
  { X := (canonicalChainData R L).complex, comon := nativeComonObj R L }

/-- The CE coalgebra under the common-universe tensor structure. Its carrier is the unchanged
canonical CE chain complex. -/
def chainCoalgebra : Comon (ChainComplex (ModuleCat.{u} R) ℕ) :=
  HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.nativeComonFunctor.obj (sourceCoalgebra R L)

@[simp]
theorem chainCoalgebra_carrier : (chainCoalgebra R L).X = ((canonicalChainData R L).complex) := rfl

/-- The converted comultiplication is the exterior chain map followed by the identity-component
tensor comparison. -/
theorem chainComul_eq :
    letI : ComonObj ((canonicalChainData R L).complex) := (chainCoalgebra R L).comon
    Δ[((canonicalChainData R L).complex)] = nativeComplexComul R L ≫
      (HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.tensorIso
        (sourceCoalgebra R L).X (sourceCoalgebra R L).X).inv := rfl

/-- The converted counit uses the down scalar map on the chain unit. -/
theorem chainCounit_eq :
    letI : ComonObj ((canonicalChainData R L).complex) := (chainCoalgebra R L).comon
    ε[((canonicalChainData R L).complex)] = nativeComplexCounit R L ≫
      (HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.unitIso (R := R)).inv := rfl

/-- The common-universe CE coaugmentation. -/
def chainCoaug : 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ) ⟶ ((canonicalChainData R L).complex) :=
  HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.nativeCoaug
    (sourceCoalgebra R L).X (nativeComplexCoaug R L)

attribute [local instance] ComonObj.instTensorUnit

/-- Coaugmentation preservation is from the CE law and the proved unit-comparison comonoid
isomorphism. -/
theorem chainCoaugIsComonHom :
    letI : ComonObj ((canonicalChainData R L).complex) := (chainCoalgebra R L).comon
    IsComonHom (chainCoaug R L) := by
  let C : HomologicalComplex.HomologyCoalgebra.LiftedUnitChain R :=
    (sourceCoalgebra R L).X
  let η : 𝟙_ (HomologicalComplex.HomologyCoalgebra.LiftedUnitChain R) ⟶ C :=
    nativeComplexCoaug R L
  letI : ComonObj C := (sourceCoalgebra R L).comon
  letI : ComonObj (𝟙_ (HomologicalComplex.HomologyCoalgebra.LiftedUnitChain R)) :=
    ComonObj.instTensorUnit _
  letI : IsComonHom η := nativeComplexCoaugIsComonHom R L
  exact HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.nativeCoaugIsComonHom C η

variable {L' : Type u} [LieRing L'] [LieAlgebra R L']

/-- The Lie map is a morphism of the fixed source CE coalgebras. -/
def sourceCoalgebraMap (f : L →ₗ⁅R⁆ L') : sourceCoalgebra R L ⟶ sourceCoalgebra R L' := by
  let C : HomologicalComplex.HomologyCoalgebra.LiftedUnitChain R := (sourceCoalgebra R L).X
  let D : HomologicalComplex.HomologyCoalgebra.LiftedUnitChain R := (sourceCoalgebra R L').X
  let g : C ⟶ D := nativeComplexMap R L f
  letI : ComonObj C := (sourceCoalgebra R L).comon
  letI : ComonObj D := (sourceCoalgebra R L').comon
  refine { hom := g, isComonHom_hom := ?_ }
  exact nativeComplexMapIsComonHom R L f

/-- The converted CE coalgebra is natural under the Lie chain map and the identity tensor
comparison. -/
def chainCoalgebraMap (f : L →ₗ⁅R⁆ L') : chainCoalgebra R L ⟶ chainCoalgebra R L' :=
  HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.nativeComonFunctor.map
    (sourceCoalgebraMap R L f)

@[simp]
theorem chainCoalgebraMap_hom (f : L →ₗ⁅R⁆ L') :
    (chainCoalgebraMap R L f).hom = nativeComplexMap R L f := rfl

@[reassoc]
theorem chainCoaug_naturality (f : L →ₗ⁅R⁆ L') :
    chainCoaug R L ≫ (chainCoalgebraMap R L f).hom = chainCoaug R L' := by
  let F := HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.toNative (R := R)
  let η : 𝟙_ (HomologicalComplex.HomologyCoalgebra.LiftedUnitChain R) ⟶
      (sourceCoalgebra R L).X := nativeComplexCoaug R L
  let g : (sourceCoalgebra R L).X ⟶ (sourceCoalgebra R L').X := nativeComplexMap R L f
  have h : η ≫ g = nativeComplexCoaug R L' := nativeComplexMap_coaug R L f
  have hMap := (F.map_comp η g).symm.trans (congrArg F.map h)
  exact (Category.assoc
    (HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.unitIso (R := R)).hom
    (F.map η) (F.map g)).trans
      (congrArg (fun z => (HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.unitIso (R := R)).hom ≫ z) hMap)

/-- The common-universe structure comparison preserves the Koszul cocommutativity equation. -/
theorem chainComul_cocommutative :
    letI : ComonObj ((canonicalChainData R L).complex) := (chainCoalgebra R L).comon
    Δ[((canonicalChainData R L).complex)] ≫ (HomologicalComplex.koszulTensorBraidingIso ((canonicalChainData R
      L).complex) ((canonicalChainData R L).complex)).hom  = Δ[((canonicalChainData R L).complex)] := by
  let C : HomologicalComplex.HomologyCoalgebra.LiftedUnitChain R := (sourceCoalgebra R L).X
  let F := HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.toNative (R := R)
  let e := HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.tensorIso C C
  let deltaMap : F.obj C ⟶ F.obj (C ⊗ C) := nativeComplexComul R L
  let b := (HomologicalComplex.koszulTensorBraidingIso (F.obj C) (F.obj C)).hom
  let bs := (HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.sourceBraiding C C).hom
  letI : ComonObj (F.obj C) := (chainCoalgebra R L).comon
  have hCom : ComonObj.comul (X := (F.obj C))  = deltaMap ≫ e.inv := chainComul_eq R L
  have hB : e.hom ≫ F.map bs = b ≫ e.hom :=
    HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.tensorIso_braiding C C
  have hS : deltaMap ≫ F.map bs  = deltaMap := nativeComplexComul_cocommutative R L
  apply (cancel_mono e.hom).1
  have hLeft := congrArg (fun z => (z ≫ b) ≫ e.hom) hCom
  have hRight := congrArg (fun z => z ≫ e.hom) hCom
  have hb' : e.inv ≫ b ≫ e.hom = F.map bs := by
    exact (Category.assoc e.inv b e.hom).symm.trans
      ((congrArg (fun t => e.inv ≫ t) hB.symm).trans
        ((Category.assoc e.inv e.hom (F.map bs)).symm.trans
          ((congrArg (fun t => t ≫ F.map bs) e.inv_hom_id).trans (Category.id_comp _))))
  have hMiddle : ((deltaMap ≫ e.inv) ≫ b) ≫ e.hom = (deltaMap ≫ e.inv) ≫ e.hom := by
    calc
      ((deltaMap ≫ e.inv) ≫ b) ≫ e.hom  = deltaMap ≫ (e.inv ≫ b ≫ e.hom) := by
        simp only [Category.assoc]
      _  = deltaMap ≫ F.map bs := congrArg (fun t => deltaMap ≫ t) hb'
      _  = deltaMap := hS
      _ = (deltaMap ≫ e.inv) ≫ e.hom := by
        exact ((Category.assoc deltaMap e.inv e.hom).trans
          ((congrArg (fun t => deltaMap ≫ t) e.inv_hom_id).trans (Category.comp_id _))).symm
  exact hLeft.trans (hMiddle.trans hRight.symm)

private theorem rightUnitTerm_compare :
    (ρ_ ((canonicalChainData R L).complex)).inv ≫ (𝟙 ((canonicalChainData R L).complex) ⊗ₘ chainCoaug R L) =
      (HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.toNative (R := R)).map ((ρ_ (sourceCoalgebra R L).X).inv ≫
        (𝟙 (sourceCoalgebra R L).X ⊗ₘ nativeComplexCoaug R L)) ≫
        (HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.tensorIso
          (sourceCoalgebra R L).X (sourceCoalgebra R L).X).inv := by
  let C : HomologicalComplex.HomologyCoalgebra.LiftedUnitChain R := (sourceCoalgebra R L).X
  let F := HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.toNative (R := R)
  let η : 𝟙_ (HomologicalComplex.HomologyCoalgebra.LiftedUnitChain R) ⟶ C := nativeComplexCoaug R L
  letI : F.Monoidal := HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.monoidal
  change (ρ_ (F.obj C)).inv ≫ (𝟙 (F.obj C) ⊗ₘ (Functor.LaxMonoidal.ε F ≫ F.map η)) =
    F.map ((ρ_ C).inv ≫ (𝟙 C ⊗ₘ η)) ≫ Functor.OplaxMonoidal.δ F C C
  rw [F.map_comp]
  simp only [id_tensorHom, Category.assoc]
  rw [← Functor.OplaxMonoidal.δ_natural_right]
  rw [← Functor.LaxMonoidal.right_unitality_inv]
  simp only [Category.assoc, id_tensorHom, MonoidalCategory.whiskerLeft_comp,
    Functor.Monoidal.μ_δ_assoc]

private theorem leftUnitTerm_compare :
    (λ_ ((canonicalChainData R L).complex)).inv ≫ (chainCoaug R L ⊗ₘ 𝟙 ((canonicalChainData R L).complex)) =
      (HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.toNative (R := R)).map ((λ_ (sourceCoalgebra R L).X).inv ≫
        (nativeComplexCoaug R L ⊗ₘ 𝟙 (sourceCoalgebra R L).X)) ≫
        (HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.tensorIso
          (sourceCoalgebra R L).X (sourceCoalgebra R L).X).inv := by
  let C : HomologicalComplex.HomologyCoalgebra.LiftedUnitChain R := (sourceCoalgebra R L).X
  let F := HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.toNative (R := R)
  let η : 𝟙_ (HomologicalComplex.HomologyCoalgebra.LiftedUnitChain R) ⟶ C := nativeComplexCoaug R L
  letI : F.Monoidal := HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.monoidal
  change (λ_ (F.obj C)).inv ≫ ((Functor.LaxMonoidal.ε F ≫ F.map η) ⊗ₘ 𝟙 (F.obj C)) =
    F.map ((λ_ C).inv ≫ (η ⊗ₘ 𝟙 C)) ≫ Functor.OplaxMonoidal.δ F C C
  rw [F.map_comp]
  simp only [tensorHom_id, Category.assoc]
  rw [← Functor.OplaxMonoidal.δ_natural_left]
  rw [← Functor.LaxMonoidal.left_unitality_inv]
  simp only [Category.assoc, tensorHom_id, MonoidalCategory.comp_whiskerRight,
    Functor.Monoidal.μ_δ_assoc]

/-- The converted primitive equation is the CE primitive equation under the tensor comparison. -/
theorem primitiveEquation_compare :
    letI : ComonObj ((canonicalChainData R L).complex) := (chainCoalgebra R L).comon
    HomologicalComplex.HomologyCoalgebra.primitiveEquation ((canonicalChainData R L).complex) (chainCoaug R L) =
      nativePrimitiveMap R L ≫
        (HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.tensorIso
          (sourceCoalgebra R L).X (sourceCoalgebra R L).X).inv := by
  letI : ComonObj ((canonicalChainData R L).complex) := (chainCoalgebra R L).comon
  change ComonObj.comul - ((ρ_ ((canonicalChainData R L).complex)).inv ≫
      (𝟙 ((canonicalChainData R L).complex) ⊗ₘ chainCoaug R L) +
      (λ_ ((canonicalChainData R L).complex)).inv ≫
      (chainCoaug R L ⊗ₘ 𝟙 ((canonicalChainData R L).complex))) = _
  rw [chainComul_eq, rightUnitTerm_compare, leftUnitTerm_compare]
  let C : HomologicalComplex.HomologyCoalgebra.LiftedUnitChain R := (sourceCoalgebra R L).X
  let F := HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.toNative (R := R)
  let e := HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.tensorIso C C
  let d : F.obj C ⟶ F.obj (C ⊗ C) := nativeComplexComul R L
  let r : C ⟶ C ⊗ C := (ρ_ C).inv ≫ (𝟙 C ⊗ₘ nativeComplexCoaug R L)
  let l : C ⟶ C ⊗ C := (λ_ C).inv ≫ (nativeComplexCoaug R L ⊗ₘ 𝟙 C)
  have h : (d ≫ e.inv) - ((F.map r ≫ e.inv) + (F.map l ≫ e.inv)) =
      (d - (F.map r + F.map l)) ≫ e.inv := by
    simp only [Preadditive.sub_comp, Preadditive.add_comp]
  exact h

/-- The converted primitive chain complex is the kernel required by the general homology
comparison. -/
def primitiveChain : (ChainComplex (ModuleCat.{u} R) ℕ) := by
  letI : ComonObj ((canonicalChainData R L).complex) := (chainCoalgebra R L).comon
  exact HomologicalComplex.HomologyCoalgebra.primitiveComplex ((canonicalChainData R L).complex) (chainCoaug R L)

/-- The old and converted primitive kernels are canonically isomorphic by the kernel map for an
isomorphism of targets. -/
def primitiveChainIso : primitiveChain R L ≅ nativePrimitiveComplex R L := by
  letI : ComonObj ((canonicalChainData R L).complex) := (chainCoalgebra R L).comon
  exact kernel.mapIso (f := HomologicalComplex.HomologyCoalgebra.primitiveEquation
    ((canonicalChainData R L).complex) (chainCoaug R L))
    (nativePrimitiveMap R L) (Iso.refl ((canonicalChainData R L).complex))
    (HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.tensorIso
      (sourceCoalgebra R L).X (sourceCoalgebra R L).X)
    (by
      have h := primitiveEquation_compare R L
      let e := HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.tensorIso
        (sourceCoalgebra R L).X (sourceCoalgebra R L).X
      exact (congrArg (fun t => t ≫ e.hom) h).trans
        ((Category.assoc (nativePrimitiveMap R L) e.inv e.hom).trans
          ((congrArg (fun t => nativePrimitiveMap R L ≫ t) e.inv_hom_id).trans (Category.comp_id _))))

@[reassoc]
theorem primitiveChainIso_inclusion :
    (primitiveChainIso R L).hom ≫ nativePrimitiveInclusion R L =
      letI : ComonObj ((canonicalChainData R L).complex) := (chainCoalgebra R L).comon
      HomologicalComplex.HomologyCoalgebra.primitiveInclusion ((canonicalChainData R L).complex) (chainCoaug R L) := by
  letI : ComonObj ((canonicalChainData R L).complex) := (chainCoalgebra R L).comon
  dsimp only [primitiveChainIso, kernel.mapIso]
  exact kernel.lift_ι _ _ _

@[reassoc]
theorem primitiveChainIso_inverse_inclusion :
    (primitiveChainIso R L).inv ≫
      (letI : ComonObj ((canonicalChainData R L).complex) := (chainCoalgebra R L).comon
       HomologicalComplex.HomologyCoalgebra.primitiveInclusion ((canonicalChainData R L).complex) (chainCoaug R L)) =
      nativePrimitiveInclusion R L := by
  rw [← primitiveChainIso_inclusion, Iso.inv_hom_id_assoc]

end UnitComparison

/-- The CE diagonal into homology of its tensor square is canonical over every commutative ring,
without invoking a Künneth isomorphism. -/
def canonicalToTensorHomology : (HomologicalComplex.Kunneth.homologyFunctor (R := R)).obj ((canonicalChainData R
  L).complex) ⟶ (HomologicalComplex.Kunneth.homologyFunctor (R := R)).obj (((canonicalChainData R L).complex) ⊗
    ((canonicalChainData R L).complex)) := by
  letI : ComonObj ((canonicalChainData R L).complex) := (UnitComparison.chainCoalgebra R L).comon
  exact HomologicalComplex.HomologyCoalgebra.canonicalToTensorHomology ((canonicalChainData R L).complex)

/-- The unconditional CE homology diagonal is natural under Lie maps. -/
@[reassoc]
theorem canonicalToTensorHomology_naturality
    {L' : Type u} [LieRing L'] [LieAlgebra R L'] (f : L →ₗ⁅R⁆ L') :
    (HomologicalComplex.Kunneth.homologyFunctor (R := R)).map (UnitComparison.chainCoalgebraMap R L f).hom ≫
      canonicalToTensorHomology R L' =
      canonicalToTensorHomology R L ≫ (HomologicalComplex.Kunneth.homologyFunctor (R := R)).map
        ((UnitComparison.chainCoalgebraMap R L f).hom ⊗ₘ
          (UnitComparison.chainCoalgebraMap R L f).hom) := by
  letI : ComonObj ((canonicalChainData R L).complex) := (UnitComparison.chainCoalgebra R L).comon
  letI : ComonObj ((canonicalChainData R L').complex) := (UnitComparison.chainCoalgebra R L').comon
  let A := UnitComparison.chainCoalgebra R L
  let B := UnitComparison.chainCoalgebra R L'
  let g : A.X ⟶ B.X := (UnitComparison.chainCoalgebraMap R L f).hom
  letI : ComonObj A.X := A.comon
  letI : ComonObj B.X := B.comon
  letI : IsComonHom g := (UnitComparison.chainCoalgebraMap R L f).isComonHom_hom
  exact HomologicalComplex.HomologyCoalgebra.canonicalToTensorHomology_naturality A.X g

/-- The canonical CE homology coaugmentation uses the two unit maps. -/
def homologyCoaug : 𝟙_ (GradedObject ℕ (ModuleCat.{u} R)) ⟶ (HomologicalComplex.Kunneth.homologyFunctor (R := R)).obj
  ((canonicalChainData R L).complex) := by
  letI : ComonObj ((canonicalChainData R L).complex) := (UnitComparison.chainCoalgebra R L).comon
  exact HomologicalComplex.HomologyCoalgebra.coaug ((canonicalChainData R L).complex) (UnitComparison.chainCoaug R L)

/-- On a free Lie module, the homology of the primitive complex in degree one is the Lie module.
The source concentration theorem is basis dependent and characteristic independent. -/
def primitiveHomologyOneIso [Module.Free R L] :
    (nativePrimitiveComplex R L).homology 1 ≅ ModuleCat.of R L :=
  HomologicalComplex.homologyMapIso (nativePrimitiveSingleIso R L) 1 ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 1
      (ModuleCat.of R (ULift.{u} L)) ≪≫
    (ULift.moduleEquiv : ULift.{u} L ≃ₗ[R] L).toModuleIso

/-- The primitive inclusion in degree one has exactly the exterior degree-one coordinate, without
any basis hypothesis. -/
theorem primitiveOne_inclusion (a : (nativePrimitiveComplex R L).X 1) :
    (nativePrimitiveInclusion R L).f 1 a =
      (exteriorPower.oneEquiv R L).symm (nativePrimitiveDegreeOneEquiv R L a) := by
  apply (exteriorPower.oneEquiv R L).injective
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Every exterior degree-one element satisfies the CE primitive equation, without a basis or
characteristic hypothesis. -/
theorem nativePrimitiveMap_one_zero : (nativePrimitiveMap R L).f 1 = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply (nativePrimitiveMap_eq_zero_iff R L 1 a).mpr
  have hp := (primitiveGenerator R L (exteriorPower.oneEquiv R L a)).property
  change (exteriorPower.oneEquiv R L).symm (exteriorPower.oneEquiv R L a) ∈ primitiveDegree R L 1 at hp
  have hEq : (exteriorPower.oneEquiv R L).symm (exteriorPower.oneEquiv R L a) =
      (show ⋀[R]^1 L from a) := LinearEquiv.symm_apply_apply _ _
  exact hEq ▸ hp

/-- The common-universe unit conversion retains the zero component of the primitive equation in
degree one. -/
theorem convertedPrimitiveMap_one_zero :
    letI : ComonObj ((canonicalChainData R L).complex) := (UnitComparison.chainCoalgebra R L).comon
    (HomologicalComplex.HomologyCoalgebra.primitiveEquation ((canonicalChainData R L).complex)
      (UnitComparison.chainCoaug R L)).f 1 = 0 := by
  have h := congrArg (fun f => f.f 1) (UnitComparison.primitiveEquation_compare R L)
  let e := HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.tensorIso
    (UnitComparison.sourceCoalgebra R L).X (UnitComparison.sourceCoalgebra R L).X
  have hv : (nativePrimitiveMap R L ≫ e.inv).f 1 = 0 :=
    (HomologicalComplex.comp_f (nativePrimitiveMap R L) e.inv 1).trans
      ((congrArg (fun t => t ≫ e.inv.f 1) (nativePrimitiveMap_one_zero R L)).trans zero_comp)
  exact h.trans hv

section Field

variable {k : Type u} [Field k] (V : Type u) [LieRing V] [LieAlgebra k V]


/-- The graded CE homology comonoid over a field. -/
def homologyComonObj : ComonObj ((HomologicalComplex.Kunneth.homologyFunctor (R := k)).obj ((canonicalChainData k
  V).complex)) := by
  letI : ComonObj ((canonicalChainData k V).complex) := (UnitComparison.chainCoalgebra k V).comon
  exact HomologicalComplex.HomologyCoalgebra.comonObjOfField ((canonicalChainData k V).complex)

/-- Lie maps preserve the constructed field homology comonoids. -/
theorem homologyMapIsComonHom {V' : Type u} [LieRing V'] [LieAlgebra k V']
    (f : V →ₗ⁅k⁆ V') :
    letI : ComonObj ((HomologicalComplex.Kunneth.homologyFunctor (R := k)).obj ((canonicalChainData k V).complex)) :=
      homologyComonObj V
    letI : ComonObj ((HomologicalComplex.Kunneth.homologyFunctor (R := k)).obj ((canonicalChainData k V').complex)) :=
      homologyComonObj V'
    let g : ((canonicalChainData k V).complex) ⟶ ((canonicalChainData k V').complex) :=
      (UnitComparison.chainCoalgebraMap k V f).hom
    IsComonHom ((HomologicalComplex.Kunneth.homologyFunctor (R := k)).map g) := by
  let C : ChainComplex (ModuleCat.{u} k) ℕ := (canonicalChainData k V).complex
  let D : ChainComplex (ModuleCat.{u} k) ℕ := (canonicalChainData k V').complex
  let H := HomologicalComplex.Kunneth.homologyFunctor (R := k)
  let g : C ⟶ D := (UnitComparison.chainCoalgebraMap k V f).hom
  letI : ComonObj C := (UnitComparison.chainCoalgebra k V).comon
  letI : ComonObj D := (UnitComparison.chainCoalgebra k V').comon
  letI : ComonObj (H.obj C) := homologyComonObj (k := k) V
  letI : ComonObj (H.obj D) := homologyComonObj (k := k) V'
  letI : IsComonHom g := (UnitComparison.chainCoalgebraMap k V f).isComonHom_hom
  letI : ∀ A B : ChainComplex (ModuleCat.{u} k) ℕ, ∀ n : ℕ,
      IsIso (HomologicalComplex.kunnethHomologyTensorMap A B n) :=
    fun A B n => HomologicalComplex.isIso_kunnethHomologyTensorMap_of_field A B n
  exact HomologicalComplex.HomologyCoalgebra.mapIsComonHom C g

/-- The canonical coaugmentation is a homology comonoid map. -/
theorem homologyCoaugIsComonHom :
    letI : ComonObj ((HomologicalComplex.Kunneth.homologyFunctor (R := k)).obj ((canonicalChainData k V).complex)) :=
      homologyComonObj V
    letI : ComonObj (𝟙_ (GradedObject ℕ (ModuleCat.{u} k))) := ComonObj.instTensorUnit (GradedObject ℕ (ModuleCat.{u}
      k))
    IsComonHom (homologyCoaug k V) := by
  letI : ComonObj ((canonicalChainData k V).complex) := (UnitComparison.chainCoalgebra k V).comon
  letI : ComonObj (𝟙_ (ChainComplex (ModuleCat.{u} k) ℕ)) :=
    ComonObj.instTensorUnit _
  letI : IsComonHom (UnitComparison.chainCoaug k V) := UnitComparison.chainCoaugIsComonHom k V
  letI : ∀ n : ℕ, IsIso (HomologicalComplex.kunnethHomologyTensorMap ((canonicalChainData k V).complex)
    ((canonicalChainData k V).complex) n) :=
    fun n => HomologicalComplex.isIso_kunnethHomologyTensorMap_of_field ((canonicalChainData k V).complex)
      ((canonicalChainData k V).complex) n
  letI : ∀ n : ℕ, IsIso (HomologicalComplex.kunnethHomologyTensorMap ((canonicalChainData k V).complex)
    (((canonicalChainData k V).complex) ⊗ ((canonicalChainData k V).complex)) n) :=
    fun n => HomologicalComplex.isIso_kunnethHomologyTensorMap_of_field ((canonicalChainData k V).complex)
      (((canonicalChainData k V).complex) ⊗ ((canonicalChainData k V).complex)) n
  exact HomologicalComplex.HomologyCoalgebra.coaugIsComonHom ((canonicalChainData k V).complex)
    (UnitComparison.chainCoaug k V)

/-- The field CE homology coalgebra as a pointed comonoid, using `Under (Comon.trivial _)` rather
than extra point/coherence inputs. -/
def homologyPointedComon : Under (Comon.trivial (GradedObject ℕ (ModuleCat.{u} k))) := by
  letI : ComonObj ((canonicalChainData k V).complex) := (UnitComparison.chainCoalgebra k V).comon
  letI : ComonObj (𝟙_ (ChainComplex (ModuleCat.{u} k) ℕ)) := ComonObj.instTensorUnit _
  letI : IsComonHom (UnitComparison.chainCoaug k V) := UnitComparison.chainCoaugIsComonHom k V
  exact HomologicalComplex.HomologyCoalgebra.coaugmentedComonOfField ((canonicalChainData k V).complex)
    (UnitComparison.chainCoaug k V)

/-- The CE homology coproduct has the canonical Koszul symmetry. -/
theorem homology_cocommutative :
    letI : ComonObj ((HomologicalComplex.Kunneth.homologyFunctor (R := k)).obj ((canonicalChainData k V).complex)) :=
      homologyComonObj V
    Δ[(HomologicalComplex.Kunneth.homologyFunctor (R := k)).obj ((canonicalChainData k V).complex)] ≫
      (HomologicalComplex.Kunneth.koszulSwap ((HomologicalComplex.Kunneth.homologyFunctor (R := k)).obj
        ((canonicalChainData k V).complex)) ((HomologicalComplex.Kunneth.homologyFunctor (R := k)).obj
          ((canonicalChainData k V).complex))).hom  = Δ[(HomologicalComplex.Kunneth.homologyFunctor (R := k)).obj
            ((canonicalChainData k V).complex)] := by
  letI : ComonObj ((canonicalChainData k V).complex) := (UnitComparison.chainCoalgebra k V).comon
  letI : ∀ n : ℕ, IsIso (HomologicalComplex.kunnethHomologyTensorMap ((canonicalChainData k V).complex)
    ((canonicalChainData k V).complex) n) :=
    fun n => HomologicalComplex.isIso_kunnethHomologyTensorMap_of_field ((canonicalChainData k V).complex)
      ((canonicalChainData k V).complex) n
  exact HomologicalComplex.HomologyCoalgebra.comul_cocommutative ((canonicalChainData k V).complex)
    (UnitComparison.chainComul_cocommutative k V)

/-- The primitive kernel in the field CE homology coalgebra. -/
def homologyPrimitiveObject : (GradedObject ℕ (ModuleCat.{u} k)) := by
  letI : ComonObj ((canonicalChainData k V).complex) := (UnitComparison.chainCoalgebra k V).comon
  letI : ∀ n : ℕ, IsIso (HomologicalComplex.kunnethHomologyTensorMap ((canonicalChainData k V).complex)
    ((canonicalChainData k V).complex) n) :=
    fun n => HomologicalComplex.isIso_kunnethHomologyTensorMap_of_field ((canonicalChainData k V).complex)
      ((canonicalChainData k V).complex) n
  exact HomologicalComplex.HomologyCoalgebra.homologyPrimitives ((canonicalChainData k V).complex)
    (UnitComparison.chainCoaug k V)

/-- The homology primitive equation is zero in degree one. This comes from its zero chain
component and the canonical transport law. -/
theorem homologyPrimitiveEquation_one_zero :
    letI : ComonObj ((canonicalChainData k V).complex) := (UnitComparison.chainCoalgebra k V).comon
    letI : ∀ n : ℕ, IsIso (HomologicalComplex.kunnethHomologyTensorMap ((canonicalChainData k V).complex)
      ((canonicalChainData k V).complex) n) :=
      fun n => HomologicalComplex.isIso_kunnethHomologyTensorMap_of_field ((canonicalChainData k V).complex)
        ((canonicalChainData k V).complex) n
    HomologicalComplex.HomologyCoalgebra.homologyPrimitiveEquation
      ((canonicalChainData k V).complex) (UnitComparison.chainCoaug k V) 1 = 0 := by
  letI : ComonObj ((canonicalChainData k V).complex) := (UnitComparison.chainCoalgebra k V).comon
  letI : ∀ n : ℕ, IsIso (HomologicalComplex.kunnethHomologyTensorMap ((canonicalChainData k V).complex)
    ((canonicalChainData k V).complex) n) :=
    fun n => HomologicalComplex.isIso_kunnethHomologyTensorMap_of_field ((canonicalChainData k V).complex)
      ((canonicalChainData k V).complex) n
  have h := congrFun (HomologicalComplex.HomologyCoalgebra.primitiveEquation_transport
    ((canonicalChainData k V).complex) (UnitComparison.chainCoaug k V)) 1
  have hc := HomologicalComplex.HomologyCoalgebra.homologyMap_eq_zero_of_component
    (HomologicalComplex.HomologyCoalgebra.primitiveEquation ((canonicalChainData k V).complex)
      (UnitComparison.chainCoaug k V)) 1
    (convertedPrimitiveMap_one_zero k V)
  have h₀ : ((HomologicalComplex.Kunneth.homologyFunctor (R := k)).map
      (HomologicalComplex.HomologyCoalgebra.primitiveEquation
        ((canonicalChainData k V).complex) (UnitComparison.chainCoaug k V))) 1 = 0 := hc
  have hEval : (((HomologicalComplex.Kunneth.homologyFunctor (R := k)).map
      (HomologicalComplex.HomologyCoalgebra.primitiveEquation
        ((canonicalChainData k V).complex) (UnitComparison.chainCoaug k V))) ≫
      inv (HomologicalComplex.Kunneth.tensorator ((canonicalChainData k V).complex)
        ((canonicalChainData k V).complex))) 1 =
      (((HomologicalComplex.Kunneth.homologyFunctor (R := k)).map
        (HomologicalComplex.HomologyCoalgebra.primitiveEquation
          ((canonicalChainData k V).complex) (UnitComparison.chainCoaug k V))) 1) ≫
        (inv (HomologicalComplex.Kunneth.tensorator ((canonicalChainData k V).complex)
          ((canonicalChainData k V).complex))) 1 := rfl
  exact h.symm.trans (hEval.trans ((congrArg (fun t => t ≫
    (inv (HomologicalComplex.Kunneth.tensorator
      ((canonicalChainData k V).complex) ((canonicalChainData k V).complex))) 1) h₀).trans zero_comp))

/-- Every CE homology class of degree one is primitive. The primitive-kernel inclusion in that
degree is an isomorphism. This does not identify it with homology of the primitive chain
complex. -/
def homologyPrimitivesOneIso : homologyPrimitiveObject V 1 ≅ ((canonicalChainData k V).complex).homology 1 := by
  letI : ComonObj ((canonicalChainData k V).complex) := (UnitComparison.chainCoalgebra k V).comon
  letI : ∀ n : ℕ, IsIso (HomologicalComplex.kunnethHomologyTensorMap ((canonicalChainData k V).complex)
    ((canonicalChainData k V).complex) n) :=
    fun n => HomologicalComplex.isIso_kunnethHomologyTensorMap_of_field ((canonicalChainData k V).complex)
      ((canonicalChainData k V).complex) n
  let φ := HomologicalComplex.HomologyCoalgebra.homologyPrimitiveEquation ((canonicalChainData k V).complex)
    (UnitComparison.chainCoaug k V)
  letI : IsIso ((kernel.ι φ) 1) := GradedObject.isIso_kernel_component_of_eq_zero
    φ 1 (homologyPrimitiveEquation_one_zero V)
  exact @asIso _ _ _ _ ((kernel.ι φ) 1)
    (GradedObject.isIso_kernel_component_of_eq_zero φ 1 (homologyPrimitiveEquation_one_zero V))

theorem homologyPrimitivesOneIso_hom :
    (homologyPrimitivesOneIso V).hom =
      (letI : ComonObj ((canonicalChainData k V).complex) := (UnitComparison.chainCoalgebra k V).comon
       letI : ∀ n : ℕ, IsIso (HomologicalComplex.kunnethHomologyTensorMap ((canonicalChainData k V).complex)
         ((canonicalChainData k V).complex) n) :=
         fun n => HomologicalComplex.isIso_kunnethHomologyTensorMap_of_field ((canonicalChainData k V).complex)
           ((canonicalChainData k V).complex) n
       kernel.ι (HomologicalComplex.HomologyCoalgebra.homologyPrimitiveEquation
         ((canonicalChainData k V).complex) (UnitComparison.chainCoaug k V))) 1 := rfl

/-- The comparison from homology of the CE primitive kernel to primitives in field CE homology. -/
def primitiveHomologyComparison :
    (HomologicalComplex.Kunneth.homologyFunctor (R := k)).obj (nativePrimitiveComplex k V) ⟶ homologyPrimitiveObject V
      := by
  letI : ComonObj ((canonicalChainData k V).complex) := (UnitComparison.chainCoalgebra k V).comon
  letI : ∀ n : ℕ, IsIso (HomologicalComplex.kunnethHomologyTensorMap ((canonicalChainData k V).complex)
    ((canonicalChainData k V).complex) n) :=
    fun n => HomologicalComplex.isIso_kunnethHomologyTensorMap_of_field ((canonicalChainData k V).complex)
      ((canonicalChainData k V).complex) n
  exact (HomologicalComplex.Kunneth.homologyFunctor (R := k)).map (UnitComparison.primitiveChainIso k V).inv ≫
    HomologicalComplex.HomologyCoalgebra.primitiveComparison ((canonicalChainData k V).complex)
      (UnitComparison.chainCoaug k V)

/-- The CE primitive comparison followed by the kernel inclusion is precisely homology of the
primitive inclusion. -/
@[reassoc]
theorem primitiveHomologyComparison_inclusion :
    primitiveHomologyComparison V ≫
      (letI : ComonObj ((canonicalChainData k V).complex) := (UnitComparison.chainCoalgebra k V).comon
       letI : ∀ n : ℕ, IsIso (HomologicalComplex.kunnethHomologyTensorMap ((canonicalChainData k V).complex)
         ((canonicalChainData k V).complex) n) :=
         fun n => HomologicalComplex.isIso_kunnethHomologyTensorMap_of_field ((canonicalChainData k V).complex)
           ((canonicalChainData k V).complex) n
       kernel.ι (HomologicalComplex.HomologyCoalgebra.homologyPrimitiveEquation
         ((canonicalChainData k V).complex) (UnitComparison.chainCoaug k V))) =
      (HomologicalComplex.Kunneth.homologyFunctor (R := k)).map (nativePrimitiveInclusion k V) := by
  letI : ComonObj ((canonicalChainData k V).complex) := (UnitComparison.chainCoalgebra k V).comon
  letI : ∀ n : ℕ, IsIso (HomologicalComplex.kunnethHomologyTensorMap ((canonicalChainData k V).complex)
    ((canonicalChainData k V).complex) n) :=
    fun n => HomologicalComplex.isIso_kunnethHomologyTensorMap_of_field ((canonicalChainData k V).complex)
      ((canonicalChainData k V).complex) n
  let C : ChainComplex (ModuleCat.{u} k) ℕ := (canonicalChainData k V).complex
  let H := HomologicalComplex.Kunneth.homologyFunctor (R := k)
  let p := HomologicalComplex.HomologyCoalgebra.primitiveComparison C (UnitComparison.chainCoaug k V)
  let i := kernel.ι (HomologicalComplex.HomologyCoalgebra.homologyPrimitiveEquation C
    (UnitComparison.chainCoaug k V))
  let g := H.map (UnitComparison.primitiveChainIso k V).inv
  have hp : p ≫ i = H.map (HomologicalComplex.HomologyCoalgebra.primitiveInclusion C
      (UnitComparison.chainCoaug k V)) :=
    HomologicalComplex.HomologyCoalgebra.primitiveComparison_ι C (UnitComparison.chainCoaug k V)
  have hMap := (H.map_comp (UnitComparison.primitiveChainIso k V).inv
    (HomologicalComplex.HomologyCoalgebra.primitiveInclusion C (UnitComparison.chainCoaug k V))).symm
  have hInc := congrArg H.map (UnitComparison.primitiveChainIso_inverse_inclusion k V)
  exact (Category.assoc g p i).trans ((congrArg (fun z => g ≫ z) hp).trans (hMap.trans hInc))

/-- The degree-one comparison starts from the Lie vector space and takes its CE homology class.
Field freeness is inferred internally. -/
def degreeOneComparison : ModuleCat.of k V ⟶ ((canonicalChainData k V).complex).homology 1 :=
  (primitiveHomologyOneIso k V).inv ≫ primitiveHomologyComparison V 1 ≫
    (homologyPrimitivesOneIso V).hom

/-- The degree-one comparison is exactly homology of the primitive inclusion in the
original-Lie-module coordinate. -/
theorem degreeOneComparison_eq : degreeOneComparison V =
    (primitiveHomologyOneIso k V).inv ≫
      HomologicalComplex.homologyMap (nativePrimitiveInclusion k V) 1 := by
  have h := congrFun (primitiveHomologyComparison_inclusion (k := k) V) 1
  have hIso := homologyPrimitivesOneIso_hom (k := k) V
  let e := (primitiveHomologyOneIso k V).inv
  have h₁ := congrArg (fun z => (e ≫ primitiveHomologyComparison (k := k) V 1) ≫ z) hIso
  have h₂ := Category.assoc e (primitiveHomologyComparison (k := k) V 1)
    ((homologyPrimitivesOneIso (k := k) V).hom)
  exact h₁.trans ((Category.assoc e (primitiveHomologyComparison (k := k) V 1) _).trans
    (congrArg (fun z => e ≫ z) h))

end Field

end ChevalleyEilenberg.HomologyCoalgebra
