/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalFunctionRestriction
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalHomotopyClasses
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SmallObject
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.HoPreNatIso

/-!
# Testing equivalences and equivalences of functor homotopy categories

The actual finite-interval testing class equals the categorical-equivalence
class tested by every quasicategory in the same value universe. Sources and
targets are arbitrary simplicial sets. The proof uses the full homotopy-class
dictionary, boundary factorization and restriction along a monic testing
map, before choosing a model structure.

This is the project pre-existence proof of Cisinski, Higher Categories and
Homotopical Algebra, Theorem 3.6.8(i),(iii), with the independent coherent
trivial-fibration input of Joyal, Propositions 1.22 and 1.27.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalClosed
universe v u
namespace SSet.joyalInterval

private lemma isomorphismClasses_bijective_of_isEquivalence
    {A B : Cat.{v, u}} (F : A ⟶ B) [F.toFunctor.IsEquivalence] :
    Function.Bijective (isomorphismClasses.map F) := by
  constructor
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro a b h
    obtain ⟨e⟩ := Quotient.exact h
    exact Quotient.sound ⟨F.toFunctor.preimageIso e⟩
  · intro y
    refine Quotient.inductionOn y ?_
    intro b
    exact ⟨Quotient.mk _ (F.toFunctor.objPreimage b),
      Quotient.sound ⟨F.toFunctor.objObjPreimageIso b⟩⟩

/-- The two actual all-probe classes agree for every original simplicial map. -/
theorem testingEquivalences_eq_categoricalEquivalences :
    productPrecylinder.{u}.testingEquivalences auxiliaryAnodyneExtensions.{u} =
      SSet.categoricalEquivalences.{u} := by
  ext X Y f
  constructor
  · intro hf
    let d := modelCategoryQuillen.monoFactorizationData f
    have hpW : productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions d.p :=
      productPrecylinder.rlp_monomorphisms_le_testingEquivalences
        auxiliaryAnodyneExtensions d.p d.hp
    have hjW : productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions d.i :=
      (productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions).of_postcomp
        d.i d.p hpW (by simpa only [d.fac] using hf)
    intro Q hQ
    let : Quasicategory Q := hQ
    have hjTC : productPrecylinder.testingTrivialCofibrations auxiliaryAnodyneExtensions d.i :=
      ⟨d.hi, hjW⟩
    have hjPre := testingTrivialCofibrations_rlp_pre (Q := Q) d.i hjTC
    have hjI : modelCategoryQuillen.I.rlp ((pre d.i).app Q) := by
      rw [← SSet.rlp_monomorphisms]
      exact hjPre
    have hjEq : (hoFunctor.map ((pre d.i).app Q)).toFunctor.IsEquivalence :=
      hoFunctor_map_isEquivalence_of_rlp_I hjI
    have hpI : modelCategoryQuillen.I.rlp d.p := by
      rw [← SSet.rlp_monomorphisms]
      exact d.hp
    have hpEq : (hoFunctor.map ((pre d.p).app Q)).toFunctor.IsEquivalence :=
      categoricalEquivalences.of_rlp_I hpI Q hQ
    let : (hoFunctor.map ((pre d.i).app Q)).toFunctor.IsEquivalence := hjEq
    let : (hoFunctor.map ((pre d.p).app Q)).toFunctor.IsEquivalence := hpEq
    rw [← d.fac, hoFunctor_pre_comp]
    infer_instance
  · intro hf Q hQ
    let : Quasicategory Q := (auxiliaryNaiveFibrantObjects_iff Q).mp hQ
    let : (hoFunctor.map ((pre f).app Q)).toFunctor.IsEquivalence := hf Q inferInstance
    have hclasses := isomorphismClasses_bijective_of_isEquivalence
      (hoFunctor.map ((pre f).app Q))
    have hmap : productPrecylinder.homotopyClassPrecomp f Q =
        fun α ↦ (homotopyClassEquivIsomorphismClasses X Q).symm
          (isomorphismClasses.map (hoFunctor.map ((pre f).app Q))
            (homotopyClassEquivIsomorphismClasses Y Q α)) := by
      funext α
      apply (homotopyClassEquivIsomorphismClasses X Q).injective
      simpa only [Equiv.apply_symm_apply] using
        homotopyClassEquivIsomorphismClasses_naturality f α
    rw [hmap]
    exact (homotopyClassEquivIsomorphismClasses X Q).symm.bijective.comp
      (hclasses.comp (homotopyClassEquivIsomorphismClasses Y Q).bijective)

end SSet.joyalInterval
