/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CyclicAlternatizationWorkingHeight
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.MatrixCyclicChainMap
public import MathlibExt.Algebra.Homology.Hochschild.Matrix.ConnesTraceWorkingHeight
public import MathlibExt.Algebra.Homology.ChainComplex.PositiveTailMapFunctor

/-!
# Lifted finite matrix cyclic trace chain maps

Let `k` be a commutative `ℚ`-algebra and `A` a unital `k`-algebra. The degree-signed cyclic
trace map from the positive tail of a finite matrix CE complex lifts to a common carrier
universe, with its cyclic quotient target lifted as well.

On a lifted wedge, the component is the lifted signed exterior representative followed by the
lifted generalized trace. Entry-algebra homomorphisms between independent carrier universes
commute with these chain maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v w z

namespace ChevalleyEilenberg

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [CommRing k] [Algebra ℚ k] (A : Type v) [Ring A] [Algebra k A]

/-- The lifted cyclic trace of a canonical positive matrix CE tail.

Use the positive-tail lift comparison, the module-functor image of the finite trace, and the
lifted cyclic quotient comparison to obtain the chosen-height chain map. -/
def matrixCyclicWeibelChainMapAtHeight (r : ℕ) :
    ChainComplex.positiveTail (matrixComplexAtHeight.{u,v,z} k A r) ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesComplexAtHeight.{u,v,z} k A :=
  ((ChainComplex.positiveTailMapFunctorIso
    (ModuleCat.uliftFunctor.{max u v z, max u v} k)).app (matrixComplex k A r)).hom ≫
      ((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (matrixCyclicWeibelChainMap k A r) ≫
          (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k A).hom

/-- The component formula for a lifted signed matrix cyclic trace.

The degree-`n` map sends a lifted wedge to its lifted degree-signed exterior representative
followed by generalized matrix trace. -/
theorem matrixCyclicWeibelChainMapAtHeight_f_up (r n : ℕ)
    (x : ⋀[k]^(n + 1) (Matrix (Fin r) (Fin r) A)) :
    ((matrixCyclicWeibelChainMapAtHeight.{u,v,z} k A r).f n).hom (ULift.up x) =
      ((ModuleCat.Algebra.Hochschild.Matrix.connesTraceAtHeight.{u,v,z} k A r).f n).hom
        (cyclicExteriorWeibelAtHeight.{u,v,z} k (Matrix (Fin r) (Fin r) A) n x) := by
  let E := HomologicalComplex.eval (ModuleCat.{max u v z} k) (ComplexShape.down ℕ) n
  let eM : (((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
        (ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k (Matrix (Fin r) (Fin r) A))).X n ≅
    (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexAtHeight.{u,v,z} k
      (Matrix (Fin r) (Fin r) A)).X n :=
    E.mapIso (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k
      (Matrix (Fin r) (Fin r) A))
  let eA : (((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A)).X n ≅
    (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexAtHeight.{u,v,z} k A).X n :=
    E.mapIso (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k A)
  have h := LinearMap.congr_fun
    (cyclicExteriorWeibelAtHeight_image.{u,v,z} k (Matrix (Fin r) (Fin r) A) n) x
  simp only [LinearMap.comp_apply] at h
  change eA.hom.hom (ULift.up (((matrixCyclicWeibelChainMap k A r).f n).hom x)) =
    eA.hom.hom (ULift.up (((ModuleCat.Algebra.Hochschild.Matrix.connesTrace k A r).f n).hom
      (eM.inv.hom (cyclicExteriorWeibelAtHeight.{u,v,z} k (Matrix (Fin r) (Fin r) A) n x)).down))
  have hInv : eM.inv.hom (eM.hom.hom
      (connesTermUpAtHeight.{u,v,z} k (Matrix (Fin r) (Fin r) A) n
        (cyclicExteriorWeibel k (Matrix (Fin r) (Fin r) A) n x))) =
    connesTermUpAtHeight.{u,v,z} k (Matrix (Fin r) (Fin r) A) n
      (cyclicExteriorWeibel k (Matrix (Fin r) (Fin r) A) n x) :=
        ModuleCat.inv_hom_apply eM _
  have hImage : cyclicExteriorWeibelAtHeight.{u,v,z} k (Matrix (Fin r) (Fin r) A) n x =
      eM.hom.hom (connesTermUpAtHeight.{u,v,z} k (Matrix (Fin r) (Fin r) A) n
        (cyclicExteriorWeibel k (Matrix (Fin r) (Fin r) A) n x)) := h
  have hInvImage := (congrArg eM.inv.hom hImage).trans hInv
  have hInvDown := congrArg (fun y => y.down) hInvImage
  rw [hInvDown]
  have hx : ((matrixCyclicWeibelChainMap k A r).f n).hom x =
      ((ModuleCat.Algebra.Hochschild.Matrix.connesTrace k A r).f n).hom
        (cyclicExteriorWeibel k (Matrix (Fin r) (Fin r) A) n x) := by
    have hf := cyclicExteriorWeibelChainMap_f k (Matrix (Fin r) (Fin r) A) n
    change ((ModuleCat.Algebra.Hochschild.Matrix.connesTrace k A r).f n).hom
        (((cyclicExteriorWeibelChainMap k (Matrix (Fin r) (Fin r) A)).f n).hom x) = _
    exact congrArg (((ModuleCat.Algebra.Hochschild.Matrix.connesTrace k A r).f n).hom)
      (LinearMap.congr_fun hf x)
  exact congrArg (fun y => eA.hom.hom (ULift.up y)) hx

variable {B : Type w} [Ring B] [Algebra k B]

/-- Coefficient naturality of lifted signed matrix cyclic traces.

The lifted positive-tail matrix coefficient map and lifted cyclic quotient map commute with
the trace, with independent source and target entry-algebra universes. -/
theorem matrixCyclicWeibelChainMapAtHeight_naturality (f : A →ₐ[k] B) (r : ℕ) :
    ChainComplex.positiveTailMap (matrixCoefficientMapAtHeight.{u,v,w,z} k A f r) ≫
        matrixCyclicWeibelChainMapAtHeight.{u,w,max u v w z} k B r =
      matrixCyclicWeibelChainMapAtHeight.{u,v,max u v w z} k A r ≫
        ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHomAtHeight.{u,v,w,z} k A
          f.toNonUnitalAlgHom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rcases x with ⟨x⟩
  change ⋀[k]^(n + 1) (Matrix (Fin r) (Fin r) A) at x
  change ((matrixCyclicWeibelChainMapAtHeight.{u,w,max u v w z} k B r).f n).hom
      (((matrixCoefficientMapAtHeight.{u,v,w,z} k A f r).f (n + 1)).hom (ULift.up x)) =
    ((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHomAtHeight.{u,v,w,z} k A
      f.toNonUnitalAlgHom).f n).hom
        (((matrixCyclicWeibelChainMapAtHeight.{u,v,max u v w z} k A r).f n).hom (ULift.up x))
  have hc := nativeLiftedComplexMapAtHeight_f_up.{u,v,w,z} k
    (Matrix (Fin r) (Fin r) A) (Matrix.coefficientLieHom k A f r) (n + 1) x
  have hcMatrix : (((matrixCoefficientMapAtHeight.{u,v,w,z} k A f r).f (n + 1)).hom
      (ULift.up x)) = ULift.up
        (exteriorPower.map (n + 1) (Matrix.coefficientLieHom k A f r).toLinearMap x) := hc
  have hMatrixB := matrixCyclicWeibelChainMapAtHeight_f_up.{u,w,max u v w z} k B r n
    (exteriorPower.map (n + 1) (Matrix.coefficientLieHom k A f r).toLinearMap x)
  have hMatrixA := matrixCyclicWeibelChainMapAtHeight_f_up.{u,v,max u v w z} k A r n x
  rw [hcMatrix]
  refine hMatrixB.trans (Eq.trans ?_
    (congrArg ((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHomAtHeight.{u,v,w,z} k A
      f.toNonUnitalAlgHom).f n).hom hMatrixA.symm))
  have hexterior := LinearMap.congr_fun (cyclicExteriorWeibelAtHeight_naturality.{u,v,w,z} k
    (Matrix (Fin r) (Fin r) A) (f.mapMatrix (m := Fin r)).toNonUnitalAlgHom n) x
  simp only [LinearMap.comp_apply] at hexterior
  have ht := congrArg (fun q => q.f n)
    (ModuleCat.Algebra.Hochschild.Matrix.connesTraceAtHeight_naturality.{u,v,w,z} k A f r)
  simp only [HomologicalComplex.comp_f] at ht
  have ht' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom ht)
    (cyclicExteriorWeibelAtHeight.{u,v,max u v w z} k (Matrix (Fin r) (Fin r) A) n x)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at ht'
  let tB := (ModuleCat.Algebra.Hochschild.Matrix.connesTraceAtHeight.{u,w,max u v w z} k B r).f n
  exact (congrArg tB.hom hexterior.symm).trans ht'.symm

end ChevalleyEilenberg
