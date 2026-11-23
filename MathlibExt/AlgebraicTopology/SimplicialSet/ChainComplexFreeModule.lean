/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import MathlibExt.Algebra.Category.ModuleCat.FinsuppCofan
public import Mathlib.SetTheory.Cardinal.UnivLE
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.Algebra.Module.ULift

/-!
# Simplicial chains as free modules

This file identifies the actual degree objects of the native simplicial chain
complex of a simplicial set with free modules on its simplices.

The construction compares the colimit cofan defining simplicial chains with
the concrete direct-sum coproduct in `ModuleCat`, then uses the linear
equivalence between direct sums and finitely supported functions. It works
over an arbitrary ring. The universe-lifted form allows simplicial sets and
coefficient rings in independent universes, while the same-universe form uses
the coefficient ring itself for convenient downstream computations. The Shrink
form keeps that same coefficient object under a weak universe bound.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped DirectSum

universe u w

namespace SSet

/-- The native degree object of simplicial chains is the direct sum of
copies of its coefficient module, indexed by the simplices. -/
noncomputable def chainComplexDirectSumIso
    {R : Type u} [Ring R] (X : SSet.{w})
    (Q : ModuleCat.{max u w} R) (n : ℕ) :
    (X.chainComplex Q).X n ≅
      (ModuleCat.of R (⨁ _ : X _⦋n⦌, Q) : ModuleCat.{max u w} R) := by
  classical
  let Z : X _⦋n⦌ → ModuleCat.{max u w} R := fun _ => Q
  exact
    (colimit.isoColimitCocone
      ⟨X.chainComplexXCofan Q n, X.isColimitChainComplexXCofan Q n⟩).symm ≪≫
        ModuleCat.coprodIsoDirectSum Z

open Classical in
/-- The direct-sum comparison sends each native simplex injection to the
corresponding direct-sum injection. -/
@[reassoc]
theorem ιChainComplex_comp_chainComplexDirectSumIso_hom
    {R : Type u} [Ring R] (X : SSet.{w})
    (Q : ModuleCat.{max u w} R)
    (n : ℕ) (x : X _⦋n⦌) :
    X.ιChainComplex (R := Q) x ≫
      (chainComplexDirectSumIso X Q n).hom =
        ModuleCat.ofHom (DirectSum.lof R (X _⦋n⦌) (fun _ => Q) x) := by
  classical
  let Z : X _⦋n⦌ → ModuleCat.{max u w} R := fun _ => Q
  let c : ColimitCocone (Discrete.functor Z) :=
    ⟨X.chainComplexXCofan Q n, X.isColimitChainComplexXCofan Q n⟩
  change X.ιChainComplex x ≫
      ((colimit.isoColimitCocone c).symm ≪≫
        ModuleCat.coprodIsoDirectSum Z).hom = _
  change c.cocone.ι.app ⟨x⟩ ≫
      (colimit.isoColimitCocone c).inv ≫
      (ModuleCat.coprodIsoDirectSum Z).hom = _
  exact (colimit.isoColimitCocone_ι_inv_assoc c ⟨x⟩
    (ModuleCat.coprodIsoDirectSum Z).hom).trans
      (ModuleCat.ι_coprodIsoDirectSum_hom Z x)

section IndependentUniverses

variable (X : SSet.{w}) (R : Type u) [Ring R]

/-- The degree-`n` object of the native simplicial chain complex with
universe-lifted coefficients is the free `R`-module on the `n`-simplices of
`X`.

The `ULift` coefficient object really belongs to
`ModuleCat.{max u w} R`; the resulting Finsupp coefficients are lowered back
to `R` through `ULift.moduleEquiv`. -/
noncomputable def chainComplexFreeIsoULift (n : ℕ) :
    (X.chainComplex
      (ModuleCat.of R (ULift.{w} R) : ModuleCat.{max u w} R)).X n ≅
      (ModuleCat.of R (X _⦋n⦌ →₀ R) : ModuleCat.{max u w} R) := by
  classical
  exact
    chainComplexDirectSumIso X
        (ModuleCat.of R (ULift.{w} R) : ModuleCat.{max u w} R) n ≪≫
      (((finsuppLEquivDirectSum R (ULift.{w} R) (X _⦋n⦌)).symm.trans
        (Finsupp.mapRange.linearEquiv
          (ULift.moduleEquiv (R := R) : ULift.{w} R ≃ₗ[R] R))).toModuleIso)

/-- Under `chainComplexFreeIsoULift`, the coproduct injection indexed by a
simplex is the basis-vector map after lowering its coefficient from `ULift R`
to `R`. -/
@[reassoc]
theorem ιChainComplex_comp_chainComplexFreeIsoULift_hom
    (n : ℕ) (x : X _⦋n⦌) :
    X.ιChainComplex
        (R := (ModuleCat.of R (ULift.{w} R) : ModuleCat.{max u w} R)) x ≫
      (chainComplexFreeIsoULift X R n).hom =
        ModuleCat.ofHom
          ((Finsupp.lsingle x (R := R) (M := R)).comp
            (ULift.moduleEquiv (R := R) : ULift.{w} R ≃ₗ[R] R).toLinearMap) := by
  classical
  rw [chainComplexFreeIsoULift, Iso.trans_hom, ← Category.assoc,
    ιChainComplex_comp_chainComplexDirectSumIso_hom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (Finsupp.mapRange.linearEquiv
      (ULift.moduleEquiv (R := R) : ULift.{w} R ≃ₗ[R] R))
        ((finsuppLEquivDirectSum R (ULift.{w} R) (X _⦋n⦌)).symm
          (DirectSum.lof R (X _⦋n⦌) (fun _ => ULift.{w} R) x r)) =
      Finsupp.single x r.down
  rw [finsuppLEquivDirectSum_symm_lof]
  simp

/-- The universe-lifted free-chain identification is natural in the
simplicial set. -/
theorem chainComplexMap_comp_chainComplexFreeIsoULift_hom
    {Y : SSet.{w}} (f : X ⟶ Y) (n : ℕ) :
    (chainComplexMap f
        (ModuleCat.of R (ULift.{w} R) : ModuleCat.{max u w} R)).f n ≫
      (chainComplexFreeIsoULift Y R n).hom =
        (chainComplexFreeIsoULift X R n).hom ≫
          ModuleCat.ofHom (Finsupp.lmapDomain R R
            (f.app (Opposite.op (SimplexCategory.mk n)))) := by
  classical
  apply chainComplex_hom_ext
  intro x
  rw [← Category.assoc, ι_chainComplexMap_f,
    ιChainComplex_comp_chainComplexFreeIsoULift_hom]
  rw [← Category.assoc,
    ιChainComplex_comp_chainComplexFreeIsoULift_hom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  simp

end IndependentUniverses

section ShrinkUniverses

private theorem shrinkCoproducts
    (R : Type u) [Ring R] [UnivLE.{w, u}] : HasCoproducts.{w} (ModuleCat.{u} R) := by
  intro I
  exact HasColimitsOfShape.of_small.{u, u} (ModuleCat.{u} R) (Discrete I)

attribute [local instance] shrinkCoproducts

variable (X : SSet.{w}) (R : Type u) [Ring R] [UnivLE.{w, u}]

/-- The native simplicial-chain module with its original coefficient object R is
free on a coefficient-sized model of the simplices. The weak universe bound
supplies Shrink.{u} indices without lifting the coefficients or the chain object. -/
def chainComplexFreeIsoShrink (n : ℕ) :
    (X.chainComplex (ModuleCat.of R R : ModuleCat.{u} R)).X n ≅
      (ModuleCat.of R (Shrink.{u} (X _⦋n⦌) →₀ R) : ModuleCat.{u} R) := by
  classical
  let I := X _⦋n⦌
  let J := Shrink.{u} I
  let j : I ≃ J := equivShrink I
  let A : ModuleCat.{u} R := ModuleCat.of R R
  let cJ : Cofan (fun _ : J => A) := ModuleCat.finsuppCofan R R J
  let hJ : IsColimit cJ := ModuleCat.finsuppCofanIsColimit R R J
  let cI : Cofan (fun _ : I => A) := Cofan.mk cJ.pt (fun x => cJ.inj (j x))
  let hI : IsColimit cI := (Cofan.isColimitEquivOfEquiv j cJ) hJ
  let hX := X.isColimitChainComplexXCofan A n
  exact hX.coconePointUniqueUpToIso hI

/-- Every native simplex injection is the basis-vector map at its Shrink index. -/
@[reassoc]
theorem ιChainComplex_comp_chainComplexFreeIsoShrink_hom (n : ℕ) (x : X _⦋n⦌) :
    X.ιChainComplex (R := (ModuleCat.of R R : ModuleCat.{u} R)) x ≫
      (chainComplexFreeIsoShrink X R n).hom =
        ModuleCat.ofHom
          (Finsupp.lsingle (equivShrink (X _⦋n⦌) x) (R := R) (M := R)) := by
  classical
  let I := X _⦋n⦌
  let J := Shrink.{u} I
  let j : I ≃ J := equivShrink I
  let A : ModuleCat.{u} R := ModuleCat.of R R
  let cJ : Cofan (fun _ : J => A) := ModuleCat.finsuppCofan R R J
  let hJ : IsColimit cJ := ModuleCat.finsuppCofanIsColimit R R J
  let cI : Cofan (fun _ : I => A) := Cofan.mk cJ.pt (fun y => cJ.inj (j y))
  let hI : IsColimit cI := (Cofan.isColimitEquivOfEquiv j cJ) hJ
  let hX := X.isColimitChainComplexXCofan A n
  let e := hX.coconePointUniqueUpToIso hI
  have h : X.ιChainComplex (R := A) x ≫ e.hom = cI.inj x :=
    hX.comp_coconePointUniqueUpToIso_hom hI (Discrete.mk x)
  with_unfolding_all exact h

/-- A Shrink-indexed basis vector returns to its same native simplex injection. -/
@[reassoc]
theorem chainComplexFreeIsoShrink_inv_single (n : ℕ) (x : X _⦋n⦌) :
    ModuleCat.ofHom
        (Finsupp.lsingle (equivShrink (X _⦋n⦌) x) (R := R) (M := R)) ≫
        (chainComplexFreeIsoShrink X R n).inv =
      X.ιChainComplex (R := (ModuleCat.of R R : ModuleCat.{u} R)) x := by
  let e := chainComplexFreeIsoShrink X R n
  let i := X.ιChainComplex (R := (ModuleCat.of R R : ModuleCat.{u} R)) x
  have h := ιChainComplex_comp_chainComplexFreeIsoShrink_hom X R n x
  exact (congrArg (fun f => f ≫ e.inv) h).symm.trans
    ((Category.assoc i e.hom e.inv).trans
      ((congrArg (fun f => i ≫ f) e.hom_inv_id).trans (Category.comp_id i)))

/-- The scalar coefficient at an actual simplex, using its Shrink coordinate. -/
def chainComplexCoefficientShrink (n : ℕ) (x : X _⦋n⦌) :
    (X.chainComplex (ModuleCat.of R R : ModuleCat.{u} R)).X n ⟶
      (ModuleCat.of R R : ModuleCat.{u} R) :=
  (chainComplexFreeIsoShrink X R n).hom ≫
    ModuleCat.ofHom (Finsupp.lapply (equivShrink (X _⦋n⦌) x))

/-- The native scalar coefficient is evaluation of the free-module coordinate. -/
theorem chainComplexCoefficientShrink_apply (n : ℕ) (x : X _⦋n⦌)
    (a : (X.chainComplex (ModuleCat.of R R : ModuleCat.{u} R)).X n) :
    (chainComplexCoefficientShrink X R n x).hom a =
      ((chainComplexFreeIsoShrink X R n).hom.hom a) (equivShrink (X _⦋n⦌) x) := rfl

open Classical in
/-- Native simplex injections satisfy the Kronecker law for Shrink coefficients. -/
@[reassoc]
theorem ιChainComplex_comp_chainComplexCoefficientShrink (n : ℕ) (x y : X _⦋n⦌) :
    X.ιChainComplex (R := (ModuleCat.of R R : ModuleCat.{u} R)) y ≫
        chainComplexCoefficientShrink X R n x =
      if y = x then 𝟙 (ModuleCat.of R R : ModuleCat.{u} R) else 0 := by
  classical
  let I := X _⦋n⦌
  let A : ModuleCat.{u} R := ModuleCat.of R R
  let e := chainComplexFreeIsoShrink X R n
  let i := X.ιChainComplex (R := A) y
  let v : A ⟶ (ModuleCat.of R (Shrink.{u} I →₀ R) : ModuleCat.{u} R) :=
    ModuleCat.ofHom (Finsupp.lsingle (equivShrink I y))
  let ev : (ModuleCat.of R (Shrink.{u} I →₀ R) : ModuleCat.{u} R) ⟶ A :=
    ModuleCat.ofHom (Finsupp.lapply (equivShrink I x))
  have hi : i ≫ e.hom = v := ιChainComplex_comp_chainComplexFreeIsoShrink_hom X R n y
  have hLeft : i ≫ chainComplexCoefficientShrink X R n x = v ≫ ev := by
    change i ≫ (e.hom ≫ ev) = v ≫ ev
    exact (Category.assoc i e.hom ev).symm.trans (congrArg (fun f => f ≫ ev) hi)
  have hEval : v ≫ ev = if y = x then 𝟙 A else 0 := by
    by_cases h : y = x
    · have hValue : v ≫ ev = 𝟙 A := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro r
        change (Finsupp.single (equivShrink I y) r) (equivShrink I x) = r
        rw [congrArg (equivShrink I) h, Finsupp.single_eq_same]
      exact hValue.trans (ite_eq_left h).symm
    · have hField : equivShrink I y ≠ equivShrink I x := by
        intro hEq
        exact h ((equivShrink I).injective hEq)
      have hValue : v ≫ ev = 0 := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro r
        change (Finsupp.single (equivShrink I y) r) (equivShrink I x) = 0
        exact Finsupp.single_eq_of_ne (Ne.symm hField)
      exact hValue.trans (ite_eq_right h).symm
  exact hLeft.trans hEval

/-- The Shrink free-chain identification is natural for every simplicial map;
its coordinate map sums coefficients over fibers of the induced simplex map. -/
theorem chainComplexMap_comp_chainComplexFreeIsoShrink_hom
    {Y : SSet.{w}} (f : X ⟶ Y) (n : ℕ) :
    (chainComplexMap f (ModuleCat.of R R : ModuleCat.{u} R)).f n ≫
      (chainComplexFreeIsoShrink Y R n).hom =
        (chainComplexFreeIsoShrink X R n).hom ≫
          ModuleCat.ofHom (Finsupp.lmapDomain R R
            (fun z : Shrink.{u} (X _⦋n⦌) =>
              equivShrink (Y _⦋n⦌)
                (f.app (op (SimplexCategory.mk n)) ((equivShrink (X _⦋n⦌)).symm z)))) := by
  classical
  apply chainComplex_hom_ext
  intro x
  rw [← Category.assoc, ι_chainComplexMap_f,
    ιChainComplex_comp_chainComplexFreeIsoShrink_hom]
  rw [← Category.assoc, ιChainComplex_comp_chainComplexFreeIsoShrink_hom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change Finsupp.single (equivShrink (Y _⦋n⦌) (f.app (op (SimplexCategory.mk n)) x)) r =
    Finsupp.mapDomain
      (fun z : Shrink.{u} (X _⦋n⦌) => equivShrink (Y _⦋n⦌)
        (f.app (op (SimplexCategory.mk n)) ((equivShrink (X _⦋n⦌)).symm z)))
      (Finsupp.single (equivShrink (X _⦋n⦌) x) r)
  simp

end ShrinkUniverses

section SameUniverse

variable (X : SSet.{u}) (R : Type u) [Ring R]

/-- The degree-`n` object of the native simplicial chain complex is the free
`R`-module on the `n`-simplices of `X`.

This convenience form uses the actual coefficient object `R` when the ring
and simplicial set live in the same universe. Use
`chainComplexFreeIsoULift` for independent universes. -/
noncomputable def chainComplexFreeIso (n : ℕ) :
    (X.chainComplex (ModuleCat.of R R : ModuleCat.{u} R)).X n ≅
      (ModuleCat.of R (X _⦋n⦌ →₀ R) : ModuleCat.{u} R) := by
  classical
  exact
    chainComplexDirectSumIso X (ModuleCat.of R R : ModuleCat.{u} R) n ≪≫
      (finsuppLEquivDirectSum R R (X _⦋n⦌)).symm.toModuleIso

/-- Under `chainComplexFreeIso`, the coproduct injection indexed by a simplex
is the corresponding Finsupp basis-vector map. -/
@[reassoc]
theorem ιChainComplex_comp_chainComplexFreeIso_hom
    (n : ℕ) (x : X _⦋n⦌) :
    X.ιChainComplex (R := (ModuleCat.of R R : ModuleCat.{u} R)) x ≫
      (chainComplexFreeIso X R n).hom =
        ModuleCat.ofHom (Finsupp.lsingle x (R := R) (M := R)) := by
  classical
  rw [chainComplexFreeIso, Iso.trans_hom, ← Category.assoc,
    ιChainComplex_comp_chainComplexDirectSumIso_hom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (finsuppLEquivDirectSum R R (X _⦋n⦌)).symm
      (DirectSum.lof R (X _⦋n⦌) (fun _ => R) x r) = Finsupp.single x r
  exact finsuppLEquivDirectSum_symm_lof R R (X _⦋n⦌) x r

/-- The free-chain identification is natural in the simplicial set. -/
theorem chainComplexMap_comp_chainComplexFreeIso_hom
    {Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    (chainComplexMap f (ModuleCat.of R R : ModuleCat.{u} R)).f n ≫
      (chainComplexFreeIso Y R n).hom =
        (chainComplexFreeIso X R n).hom ≫
          ModuleCat.ofHom (Finsupp.lmapDomain R R
            (f.app (Opposite.op (SimplexCategory.mk n)))) := by
  classical
  apply chainComplex_hom_ext
  intro x
  rw [← Category.assoc, ι_chainComplexMap_f,
    ιChainComplex_comp_chainComplexFreeIso_hom]
  rw [← Category.assoc,
    ιChainComplex_comp_chainComplexFreeIso_hom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  simp

end SameUniverse

end SSet
