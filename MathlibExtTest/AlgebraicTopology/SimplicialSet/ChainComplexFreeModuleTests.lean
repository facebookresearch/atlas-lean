/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.ChainComplexFreeModule
import Mathlib.Data.Matrix.Mul

/-!
# Free-chain clients

The coefficient ring is noncommutative and the simplicial set has infinitely
many simplices in every degree. Collapsing two distinct simplices must add
their coefficients, exercising naturality for a noninjective simplicial map.
-/

open CategoryTheory Opposite
open CategoryTheory.Limits
open scoped Simplicial

noncomputable section

namespace MathlibExtTest.ChainComplexFreeModule

universe u w

section IndependentUniverses

variable (S : Type u) [Ring S] (U : SSet.{w})

example (n : ℕ) :
    (U.chainComplex
      (ModuleCat.of S (ULift.{w} S) : ModuleCat.{max u w} S)).X n ≅
      (ModuleCat.of S (U _⦋n⦌ →₀ S) : ModuleCat.{max u w} S) :=
  SSet.chainComplexFreeIsoULift U S n

example (n : ℕ) (x : U _⦋n⦌) :
    U.ιChainComplex
        (R := (ModuleCat.of S (ULift.{w} S) : ModuleCat.{max u w} S)) x ≫
      (SSet.chainComplexFreeIsoULift U S n).hom =
        ModuleCat.ofHom
          ((Finsupp.lsingle x (R := S) (M := S)).comp
            (ULift.moduleEquiv (R := S) : ULift.{w} S ≃ₗ[S] S).toLinearMap) :=
  SSet.ιChainComplex_comp_chainComplexFreeIsoULift_hom U S n x

example {V : SSet.{w}} (f : U ⟶ V) (n : ℕ) :
    (SSet.chainComplexMap f
        (ModuleCat.of S (ULift.{w} S) : ModuleCat.{max u w} S)).f n ≫
      (SSet.chainComplexFreeIsoULift V S n).hom =
        (SSet.chainComplexFreeIsoULift U S n).hom ≫
          ModuleCat.ofHom (Finsupp.lmapDomain S S
            (f.app (Opposite.op (SimplexCategory.mk n)))) :=
  SSet.chainComplexMap_comp_chainComplexFreeIsoULift_hom U S f n

end IndependentUniverses

section ShrinkUniverses

private theorem callerShrinkCoproducts
    (S : Type u) [Ring S] [UnivLE.{w, u}] : CategoryTheory.Limits.HasCoproducts.{w} (ModuleCat.{u} S) := by
  intro I
  exact HasColimitsOfShape.of_small.{u, u} (ModuleCat.{u} S) (Discrete I)

attribute [local instance] callerShrinkCoproducts

variable (S : Type u) [Ring S] (U : SSet.{w}) [UnivLE.{w, u}]

example (n : ℕ) :
    (U.chainComplex (ModuleCat.of S S : ModuleCat.{u} S)).X n ≅
      (ModuleCat.of S (Shrink.{u} (U _⦋n⦌) →₀ S) : ModuleCat.{u} S) :=
  SSet.chainComplexFreeIsoShrink U S n

example (n : ℕ) (x : U _⦋n⦌) :
    U.ιChainComplex (R := (ModuleCat.of S S : ModuleCat.{u} S)) x ≫
      (SSet.chainComplexFreeIsoShrink U S n).hom =
        ModuleCat.ofHom
          (Finsupp.lsingle (equivShrink (U _⦋n⦌) x) (R := S) (M := S)) :=
  SSet.ιChainComplex_comp_chainComplexFreeIsoShrink_hom U S n x

open Classical in
example (n : ℕ) (x y : U _⦋n⦌) (a b : S) (hy : y ≠ x) :
    (SSet.chainComplexCoefficientShrink U S n x).hom
      ((U.ιChainComplex (R := (ModuleCat.of S S : ModuleCat.{u} S)) x).hom a +
        (U.ιChainComplex (R := (ModuleCat.of S S : ModuleCat.{u} S)) y).hom b) = a := by
  let c := SSet.chainComplexCoefficientShrink U S n x
  let ix := U.ιChainComplex (R := (ModuleCat.of S S : ModuleCat.{u} S)) x
  let iy := U.ιChainComplex (R := (ModuleCat.of S S : ModuleCat.{u} S)) y
  have hxMap : ix ≫ c = 𝟙 (ModuleCat.of S S : ModuleCat.{u} S) :=
    (SSet.ιChainComplex_comp_chainComplexCoefficientShrink U S n x x).trans
      (ite_eq_left rfl)
  have hyMap : iy ≫ c = 0 :=
    (SSet.ιChainComplex_comp_chainComplexCoefficientShrink U S n x y).trans
      (ite_eq_right hy)
  have hxValue : c.hom (ix.hom a) = a := congrArg (fun f => f.hom a) hxMap
  have hyValue : c.hom (iy.hom b) = 0 := congrArg (fun f => f.hom b) hyMap
  exact (c.hom.map_add _ _).trans
    ((congrArg₂ (· + ·) hxValue hyValue).trans (add_zero a))

end ShrinkUniverses

private abbrev R := Matrix (Fin 2) (Fin 2) ℤ

private abbrev discrete : SSet where
  obj _ := ℕ
  map _ := 𝟙 ℕ

private abbrev point : SSet where
  obj _ := PUnit
  map _ := 𝟙 PUnit

private def collapse : discrete ⟶ point where
  app _ := TypeCat.ofHom (fun (_ : ℕ) => PUnit.unit)

example (n : ℕ) (r s : R) :
    (SSet.chainComplexFreeIso point R n).hom.hom
      (((SSet.chainComplexMap collapse (ModuleCat.of R R)).f n).hom
        ((discrete.ιChainComplex (n := n) (R := ModuleCat.of R R) 0).hom r +
          (discrete.ιChainComplex (n := n) (R := ModuleCat.of R R) 1).hom s)) =
      Finsupp.single PUnit.unit (r + s) := by
  have hbasis (x : ℕ) (a : R) :
      (SSet.chainComplexFreeIso discrete R n).hom.hom
          ((discrete.ιChainComplex (n := n) (R := ModuleCat.of R R) x).hom a) =
        Finsupp.single x a :=
    ConcreteCategory.congr_hom
      (SSet.ιChainComplex_comp_chainComplexFreeIso_hom discrete R n x) a
  calc
    _ = Finsupp.lmapDomain R R (collapse.app (op (SimplexCategory.mk n)))
        ((SSet.chainComplexFreeIso discrete R n).hom.hom
          ((discrete.ιChainComplex (n := n) (R := ModuleCat.of R R) 0).hom r +
            (discrete.ιChainComplex (n := n) (R := ModuleCat.of R R) 1).hom s)) :=
      ConcreteCategory.congr_hom
        (SSet.chainComplexMap_comp_chainComplexFreeIso_hom discrete R collapse n) _
    _ = Finsupp.single PUnit.unit (r + s) := by
      rw [map_add, hbasis, hbasis]
      simp [collapse, Finsupp.mapDomain_add]

section ShrinkCollapse

attribute [local instance] callerShrinkCoproducts

example (n : ℕ) (r s : R) :
    (SSet.chainComplexFreeIsoShrink point R n).hom.hom
      (((SSet.chainComplexMap collapse (ModuleCat.of R R)).f n).hom
        ((discrete.ιChainComplex (n := n) (R := ModuleCat.of R R) 0).hom r +
          (discrete.ιChainComplex (n := n) (R := ModuleCat.of R R) 1).hom s)) =
      Finsupp.single (equivShrink (point _⦋n⦌) PUnit.unit) (r + s) := by
  let index : Shrink (discrete _⦋n⦌) → Shrink (point _⦋n⦌) := fun z =>
    equivShrink (point _⦋n⦌)
      (collapse.app (op (SimplexCategory.mk n)) ((equivShrink (discrete _⦋n⦌)).symm z))
  have hbasis (x : ℕ) (a : R) :
      (SSet.chainComplexFreeIsoShrink discrete R n).hom.hom
        ((discrete.ιChainComplex (n := n) (R := ModuleCat.of R R) x).hom a) =
          Finsupp.single (equivShrink (discrete _⦋n⦌) x) a :=
    ConcreteCategory.congr_hom
      (SSet.ιChainComplex_comp_chainComplexFreeIsoShrink_hom discrete R n x) a
  calc
    _ = Finsupp.lmapDomain R R index
        ((SSet.chainComplexFreeIsoShrink discrete R n).hom.hom
          ((discrete.ιChainComplex (n := n) (R := ModuleCat.of R R) 0).hom r +
            (discrete.ιChainComplex (n := n) (R := ModuleCat.of R R) 1).hom s)) :=
      ConcreteCategory.congr_hom
        (SSet.chainComplexMap_comp_chainComplexFreeIsoShrink_hom discrete R collapse n) _
    _ = Finsupp.single (equivShrink (point _⦋n⦌) PUnit.unit) (r + s) := by
      rw [map_add, hbasis, hbasis]
      simp [index, collapse, Finsupp.mapDomain_add]

end ShrinkCollapse

end MathlibExtTest.ChainComplexFreeModule
