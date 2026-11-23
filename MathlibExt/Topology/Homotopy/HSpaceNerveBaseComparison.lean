/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.HSpaceHomologyOne
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.PiZeroMapEndCriterion
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveEquivalenceWeakEquivalence

/-!
# The actual groupoid-nerve base comparison from integral H₁

For an arbitrary map between path-connected H-spaces, the verified integral
H₁ comparison derives bijectivity of the original fundamental-group map.
The existing singular naturality formula, with its computed image-point
isomorphism, transfers this to the raw singular groupoid endomorphism map.
The existing π₀/map-End criterion then proves equivalence of the actual
fundamental groupoids and weakness of the actual map of their nerves.

This is a base comparison for the regular-cover spectral argument. It does
not claim that integral H₁ alone makes the original map a weak equivalence.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology

universe u

public section

namespace TopCat.HSpaceHomologyOne

private theorem singular_basedEndMap_bijective
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : X ⟶ Y)
    (hf : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor 1).map f)) (x : X) :
    Function.Bijective
      (SSet.basedFundamentalGroupHom (TopCat.toSSet.map f)
        (TopCat.toSSetObj₀Equiv.symm x) (TopCat.toSSetObj₀Equiv.symm (f x))
        (TopCat.singularMappedVertexIso f x)) := by
  let EX := TopCat.singularFundamentalGroupoidEndMulEquiv X x
  let EY := TopCat.singularFundamentalGroupoidEndMulEquiv Y (f x)
  let p := FundamentalGroup.mapOfEq f.hom (x := x) (y := f x) rfl
  let B := SSet.basedFundamentalGroupHom (TopCat.toSSet.map f)
    (TopCat.toSSetObj₀Equiv.symm x) (TopCat.toSSetObj₀Equiv.symm (f x))
    (TopCat.singularMappedVertexIso f x)
  have hp : Function.Bijective p :=
    fundamentalGroupMap_bijective_of_integralHomologyOne_isIso f hf x
  have hValue (q) : B q = EY.symm (p (EX q)) :=
    ((TopCat.singularEnd_inverse_naturality f x (EX q)).trans
      (congrArg B (EX.symm_apply_apply q))).symm
  constructor
  · intro a b h
    apply EX.injective
    apply hp.1
    apply EY.symm.injective
    exact (hValue a).symm.trans (h.trans (hValue b))
  · intro b
    obtain ⟨a, ha⟩ := hp.2 (EY b)
    refine ⟨EX.symm a, (hValue (EX.symm a)).trans ?_⟩
    exact (congrArg (fun z => EY.symm (p z)) (EX.apply_symm_apply a)).trans
      ((congrArg EY.symm ha).trans (EY.symm_apply_apply b))

private theorem singular_rawEndMap_bijective
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : X ⟶ Y)
    (hf : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor 1).map f)) (x : X) :
    Function.Bijective ((SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)).map
      (X := SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm x))
      (Y := SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm x))) := by
  let F := SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)
  let sx := TopCat.toSSetObj₀Equiv.symm x
  let sy := TopCat.toSSetObj₀Equiv.symm (f x)
  let e := TopCat.singularMappedVertexIso f x
  let B := SSet.basedFundamentalGroupHom (TopCat.toSSet.map f) sx sy e
  let M := F.mapEnd (SSet.FundamentalGroupoid.mk sx)
  have hB : Function.Bijective B := singular_basedEndMap_bijective f hf x
  have hFactor (q) : B q = e.conj (M q) := by
    apply End.ext
    rw [SSet.basedFundamentalGroupHom_apply, CategoryTheory.Iso.conj_apply_asHom]
    rfl
  have hM : Function.Bijective M := by
    constructor
    · intro a b h
      apply hB.1
      exact (hFactor a).trans ((congrArg e.conj h).trans (hFactor b).symm)
    · intro b
      obtain ⟨a, ha⟩ := hB.2 (e.conj b)
      exact ⟨a, e.conj.injective ((hFactor a).symm.trans ha)⟩
  constructor
  · intro a b h
    have hEnd : M (End.of a) = M (End.of b) := by
      apply End.ext
      exact h
    exact congrArg End.asHom (hM.1 hEnd)
  · intro b
    obtain ⟨a, ha⟩ := hM.2 (End.of b)
    exact ⟨a.asHom, congrArg End.asHom ha⟩

/-- Integral H₁ alone derives the actual whole singular groupoid equivalence
for any original map between connected H-spaces. No H-map is required. -/
theorem isEquivalence_singularFundamentalGroupoid_of_integralHomologyOne_isIso
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : X ⟶ Y)
    (hf : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor 1).map f)) :
    (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)).IsEquivalence := by
  let SX := TopCat.toSSet.obj X
  let SY := TopCat.toSSet.obj Y
  let sf := TopCat.toSSet.map f
  let : SX.IsConnected := inferInstance
  let : SY.IsConnected := inferInstance
  have hZero : Function.Bijective (SSet.mapπ₀ sf) := by
    constructor
    · intro a b _
      exact Subsingleton.elim a b
    · intro b
      refine ⟨SSet.π₀.mk (TopCat.toSSetObj₀Equiv.symm (HSpace.e : X)), ?_⟩
      exact Subsingleton.elim _ _
  apply SSet.isEquivalence_mapFundamentalGroupoid_of_bijective_mapπ₀_mapEnd sf hZero
  intro sx
  obtain ⟨x, rfl⟩ := (TopCat.toSSetObj₀Equiv (X := X)).symm.surjective sx
  exact singular_rawEndMap_bijective f hf x

/-- The actual nerve base map is weak, derived from the integral-H₁ input
and the existing categorical nerve-equivalence theorem. -/
theorem nerveBaseMap_mem_realizationWeakEquivalences_of_integralHomologyOne_isIso
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : X ⟶ Y)
    (hf : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor 1).map f)) :
    SSet.realizationWeakEquivalences
      (CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f))) := by
  let F := SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)
  let : F.IsEquivalence :=
      isEquivalence_singularFundamentalGroupoid_of_integralHomologyOne_isIso f hf
  exact CategoryTheory.nerveMap_mem_realizationWeakEquivalences_of_isEquivalence F

end TopCat.HSpaceHomologyOne
