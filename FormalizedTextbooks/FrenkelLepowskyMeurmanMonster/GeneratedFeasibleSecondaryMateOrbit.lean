/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryDisjointPairDestination
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryContainingOctadDestination
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryOutsideOctadDestination
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryOddDestination

/-! The two signed actual mate axes are separate singleton simultaneous orbits. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The actual simultaneous vector action, selected before generic pointwise function actions. -/
noncomputable instance (priority := 2000) generatedFeasibleSecondaryNActualSmul :
    SMul ↥(localAxisStabilizer generatedFeasiblePhysicalRootPair ⊓ localOmegaStabilizer)
      GriessSpace where
  smul h x := rhoLocal h.val x

/-- The same genuine action is the restriction of the original H action by subgroup inclusion. -/
noncomputable instance generatedFeasibleSecondaryNActualAction :
    MulAction ↥(localAxisStabilizer generatedFeasiblePhysicalRootPair ⊓ localOmegaStabilizer)
      GriessSpace :=
  MulAction.compHom GriessSpace
    (localAxisStabilizer generatedFeasiblePhysicalRootPair ⊓ localOmegaStabilizer).subtype

/-- The original preferred plus-pair mate of the fixed minus-pair root. -/
def generatedFeasibleMateLabel : GriessShortIndex := Sum.inl (1, generatedFeasiblePhysicalRootPair)

/-- The actual central correction in the product of the original Omega and first preferred Q. -/
def generatedFeasibleMateCentralPhase : ZMod 2 :=
  -toAdd (sourceOmegaQ * griessShortQ (Sum.inl (0, generatedFeasiblePhysicalRootPair))).coeff

/-- The genuine mate Q is the Omega/first product with its entire original central phase
retained. -/
theorem generatedFeasibleMate_Q_product : griessShortQ generatedFeasibleMateLabel =
    qCentral generatedFeasibleMateCentralPhase *
      (sourceOmegaQ * griessShortQ (Sum.inl (0, generatedFeasiblePhysicalRootPair))) := by
  apply NormalizedCocycleExtension.Extension.ext
  · rw [qCentral_mul_base]
    apply toAdd.injective
    rw [NormalizedCocycleExtension.mul_base, toAdd_mul]
    exact generatedFeasible_pair_mate_base
  · apply toAdd.injective
    rw [qCentral_mul_coeff]
    change (0 : ZMod 2) = -toAdd
      (sourceOmegaQ * griessShortQ (Sum.inl (0, generatedFeasiblePhysicalRootPair))).coeff +
        toAdd (sourceOmegaQ * griessShortQ (Sum.inl (0, generatedFeasiblePhysicalRootPair))).coeff
    exact (neg_add_cancel _).symm

/-- Any actual fiber fixing the first axis and centralizing Omega fixes the entire preferred mate Q.
-/
theorem generatedFeasibleMate_Q_fixed (f : localFiberSubgroup)
    (hfirst : localFiberIntoH f ∈ localAxisStabilizer generatedFeasiblePhysicalRootPair)
    (hOmega : localFiberIntoH f ∈ localOmegaStabilizer) :
    spinConjugation f.val.1 (griessShortQ generatedFeasibleMateLabel) =
      griessShortQ generatedFeasibleMateLabel := by
  have hp := (localAxisStabilizer_mk_iff f generatedFeasiblePhysicalRootPair).mp hfirst
  have hq : spinConjugation f.val.1
      (griessShortQ (Sum.inl (0, generatedFeasiblePhysicalRootPair))) =
        griessShortQ (Sum.inl (0, generatedFeasiblePhysicalRootPair)) := by
    rw [griessShortQ_image, hp.1, hp.2]
    change (1 : Q) * griessShortQ (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = _
    exact one_mul _
  have hO := (localOmegaStabilizer_fiber_iff f).mp hOmega
  rw [generatedFeasibleMate_Q_product, map_mul, spinConjugation_central, map_mul, hO, hq]

/-- The original preferred mate acquires no actual short phase under any simultaneous fixer. -/
theorem generatedFeasibleMate_phase_zero (f : localFiberSubgroup)
    (hfirst : localFiberIntoH f ∈ localAxisStabilizer generatedFeasiblePhysicalRootPair)
    (hOmega : localFiberIntoH f ∈ localOmegaStabilizer) :
    localShortPhase f generatedFeasibleMateLabel = 0 := by
  change toAdd (spinConjugation f.val.1 (griessShortQ generatedFeasibleMateLabel)).coeff = 0
  rw [generatedFeasibleMate_Q_fixed f hfirst hOmega]
  rfl

/-- Each signed actual mate axis is fixed individually by the entire simultaneous stabilizer. -/
theorem generatedFeasibleMate_axis_fixed
    (h : ↥(localAxisStabilizer generatedFeasiblePhysicalRootPair ⊓ localOmegaStabilizer))
    (c : ZMod 2) :
    rhoLocal h.val (conwayShortAxis generatedFeasibleMateLabel c) =
      conwayShortAxis generatedFeasibleMateLabel c := by
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
  change localFiberIntoH f = h.val at hf
  have hfirst : localFiberIntoH f ∈ localAxisStabilizer generatedFeasiblePhysicalRootPair :=
    hf.symm ▸ h.property.1
  have hO : localFiberIntoH f ∈ localOmegaStabilizer := hf.symm ▸ h.property.2
  have hmon := generatedFeasible_localOmega_lift_monomial f hO
  have hp := (localAxisStabilizer_mk_iff f generatedFeasiblePhysicalRootPair).mp hfirst
  have hm := (generatedFeasible_monomial_pair_fix_iff f.val.2 hmon).mp hp.1
  change griessShortPermutation f.val.2 generatedFeasibleMateLabel =
    generatedFeasibleMateLabel at hm
  have hi := generatedAxis_localFiber_image f generatedFeasibleMateLabel c
  rw [hm, generatedFeasibleMate_phase_zero f hfirst hO, zero_add] at hi
  rw [← hf]
  exact hi

/-- The genuine simultaneous orbit of either actual signed mate axis. -/
def generatedFeasibleMateOrbit (c : ZMod 2) : Set GriessSpace :=
  Set.range (fun h : ↥(localAxisStabilizer generatedFeasiblePhysicalRootPair ⊓
      localOmegaStabilizer) => rhoLocal h.val (conwayShortAxis generatedFeasibleMateLabel c))

/-- Each actual signed mate has precisely its singleton simultaneous orbit. -/
theorem generatedFeasibleMateOrbit_eq_singleton (c : ZMod 2) :
    generatedFeasibleMateOrbit c = {conwayShortAxis generatedFeasibleMateLabel c} := by
  ext x
  constructor
  · rintro ⟨h, rfl⟩
    apply Set.mem_singleton_iff.mpr
    exact generatedFeasibleMate_axis_fixed h c
  · intro hx
    have he := Set.mem_singleton_iff.mp hx
    subst x
    refine ⟨1, ?_⟩
    change rhoLocal (1 : H) _ = _
    rw [map_one]
    rfl

/-- Each genuine signed mate simultaneous orbit contains exactly one actual axis. -/
theorem generatedFeasibleMateOrbit_card (c :
    ZMod 2) : Nat.card (generatedFeasibleMateOrbit c) = 1 := by
  rw [generatedFeasibleMateOrbit_eq_singleton, Nat.card_eq_fintype_card]
  exact Fintype.card_unique

/-- The two actual signed mate orbits are disjoint, rather than a presumed two-element orbit. -/
theorem generatedFeasibleMateOrbit_disjoint (c d : ZMod 2) (hcd : c ≠ d) :
    Disjoint (generatedFeasibleMateOrbit c) (generatedFeasibleMateOrbit d) := by
  rw [generatedFeasibleMateOrbit_eq_singleton, generatedFeasibleMateOrbit_eq_singleton]
  apply Set.disjoint_singleton.mpr
  intro he
  have hh := @generatedAxis_signed_injective
    (generatedFeasibleMateLabel, c) (generatedFeasibleMateLabel, d) he
  exact hcd (congrArg (fun z : GriessShortIndex × ZMod 2 => z.2) hh)

/-- The actual two signed mate axes in the original secondary physical catalogue. -/
def generatedFeasibleMateSignedAxes : Set GriessSpace :=
  Set.range (fun c : ZMod 2 => conwayShortAxis generatedFeasibleMateLabel c)

/-- There are exactly two distinct actual signed mate axes. -/
theorem generatedFeasibleMateSignedAxes_card : Nat.card generatedFeasibleMateSignedAxes = 2 := by
  let f := fun c : ZMod 2 => conwayShortAxis generatedFeasibleMateLabel c
  have hf : Function.Injective f := by
    intro c d he
    have hh := @generatedAxis_signed_injective
      (generatedFeasibleMateLabel, c) (generatedFeasibleMateLabel, d) he
    exact congrArg (fun z : GriessShortIndex × ZMod 2 => z.2) hh
  change Nat.card (Set.range f) = 2
  rw [← Nat.card_congr (Equiv.ofInjective f hf), Nat.card_eq_fintype_card, ZMod.card]

/-- Both original signed mates belong to the genuine complete secondary feasible orbit. -/
theorem generatedFeasibleMate_axis_mem (c : ZMod 2) :
    conwayShortAxis generatedFeasibleMateLabel c ∈
      generatedFeasibleSecondaryLocalOrbit generatedFeasiblePhysicalRootPair := by
  rw [generatedFeasibleSecondaryLocalOrbit_eq_physical]
  refine ⟨⟨(generatedFeasibleMateLabel, c), ?_⟩, rfl⟩
  refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
  simpa only [generatedFeasibleMateLabel, generatedFeasibleOrthogonalShortLabels,
    Finset.inl_mem_disjSum] using generatedFeasibleDisjointPair_mate_mem

/-- The genuine original extra-generator destination of each of the two signed mates. -/
def generatedFeasibleMateDestination (c : ZMod 2) : GriessSpace :=
  sExtra (conwayShortAxis generatedFeasibleMateLabel c)

/-- Each actual signed mate has its original source-defined triality destination. -/
theorem generatedFeasibleMate_triality_destination (c : ZMod 2) :
    ∃ h : localAxisStabilizer generatedFeasiblePhysicalRootPair,
      rhoLocal h.val (sExtra (conwayShortAxis generatedFeasibleMateLabel c)) =
        generatedFeasibleMateDestination c := by
  refine ⟨1, ?_⟩
  change rhoLocal (1 : H) _ = _
  rw [map_one]
  rfl

/-- The first signed mate goes to the actual opposite signed first-root axis. -/
theorem generatedFeasibleMateDestination_zero : generatedFeasibleMateDestination 0 =
    conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1 := by
  rw [generatedFeasibleMateDestination, generatedFeasibleMateLabel,
    generatedAxis_triality_pair_exact]
  norm_num

/-- The second signed mate returns to the original positive-sign preferred mate axis. -/
theorem generatedFeasibleMateDestination_one : generatedFeasibleMateDestination 1 =
    conwayShortAxis generatedFeasibleMateLabel 0 := by
  rw [generatedFeasibleMateDestination, generatedFeasibleMateLabel,
    generatedAxis_triality_pair_exact]
  norm_num

/-- The returning signed mate destination belongs to the original secondary feasible orbit. -/
theorem generatedFeasibleMateDestination_one_mem : generatedFeasibleMateDestination 1 ∈
    generatedFeasibleSecondaryLocalOrbit generatedFeasiblePhysicalRootPair := by
  rw [generatedFeasibleMateDestination_one]
  exact generatedFeasibleMate_axis_mem 0

/-- Triality fixes the genuine disjoint minus-pair prototype, giving its actual return destination.
-/
theorem generatedFeasibleDisjointPairDestination_eq_prototype :
    generatedFeasibleDisjointPairDestination =
      conwayShortAxis generatedFeasibleDisjointPairPrototypeLabel 0 := by
  rw [generatedFeasibleDisjointPairDestination, generatedFeasibleDisjointPairPrototypeLabel,
    generatedAxis_triality_pair_exact]
  norm_num

/-- The whole original disjoint-pair destination is in the actual secondary feasible orbit. -/
theorem generatedFeasibleDisjointPairDestination_mem : generatedFeasibleDisjointPairDestination ∈
    generatedFeasibleSecondaryLocalOrbit generatedFeasiblePhysicalRootPair := by
  rw [generatedFeasibleDisjointPairDestination_eq_prototype]
  exact generatedFeasibleDisjointPair_axis_mem
    (0, generatedFeasibleDisjointPairPrototypeIndex) generatedFeasibleDisjointPairPrototype_mem 0

/-- The two original source destinations are distinct actual vectors; no A-orbit classification
is asserted by this statement. -/
theorem generatedFeasibleMateDestination_injective :
    Function.Injective generatedFeasibleMateDestination := by
  intro c d he
  have hh := @generatedAxis_signed_injective
    (generatedFeasibleMateLabel, c) (generatedFeasibleMateLabel, d) (sExtra.injective he)
  exact congrArg (fun z : GriessShortIndex × ZMod 2 => z.2) hh

/-- The six genuine simultaneous orbit prototypes: the two mates, disjoint pairs,
containing octads, outside octads, and original odd vectors. -/
def generatedFeasibleSecondaryNPrototype : Fin 6 → GriessSpace :=
  ![conwayShortAxis generatedFeasibleMateLabel 0,
    conwayShortAxis generatedFeasibleMateLabel 1,
    conwayShortAxis generatedFeasibleDisjointPairPrototypeLabel 0,
    conwayShortAxis generatedFeasibleContainingOctadPrototypeLabel 0,
    conwayShortAxis generatedFeasibleOutsideOctadPrototypeLabel 0,
    conwayShortAxis generatedFeasibleSecondaryOddPrototypeLabel 0]

/-- Six actual simultaneous orbits in the original secondary physical geometry. -/
def generatedFeasibleSecondaryNOrbit (k : Fin 6) : Set GriessSpace :=
  match k with
  | 0 => generatedFeasibleMateOrbit 0
  | 1 => generatedFeasibleMateOrbit 1
  | 2 => generatedFeasibleDisjointPairOrbit
  | 3 => generatedFeasibleContainingOctadOrbit
  | 4 => generatedFeasibleOutsideOctadOrbit
  | _ => generatedFeasibleSecondaryOddOrbit

/-- Every displayed sector is the orbit of its actual prototype under the same original group. -/
theorem generatedFeasibleSecondaryNOrbit_eq (k : Fin 6) :
    generatedFeasibleSecondaryNOrbit k =
      MulAction.orbit
        ↥(localAxisStabilizer generatedFeasiblePhysicalRootPair ⊓ localOmegaStabilizer)
        (generatedFeasibleSecondaryNPrototype k) := by
  fin_cases k <;> rfl

/-- Original cardinality values, proved individually for the actual six simultaneous orbits. -/
def generatedFeasibleSecondaryNOrbitSize : Fin 6 → ℕ := ![1, 1, 924, 4928, 42240, 45056]

/-- Each actual simultaneous orbit has its proved original source cardinality. -/
theorem generatedFeasibleSecondaryNOrbit_card (k : Fin 6) :
    Nat.card (generatedFeasibleSecondaryNOrbit k) = generatedFeasibleSecondaryNOrbitSize k := by
  fin_cases k
  · exact generatedFeasibleMateOrbit_card 0
  · exact generatedFeasibleMateOrbit_card 1
  · exact generatedFeasibleDisjointPairOrbit_card
  · exact generatedFeasibleContainingOctadOrbit_card
  · exact generatedFeasibleOutsideOctadOrbit_card
  · exact generatedFeasibleSecondaryOddOrbit_card

/-- Every original prototype belongs to the actual complete secondary feasible orbit. -/
theorem generatedFeasibleSecondaryNPrototype_mem (k : Fin 6) :
    generatedFeasibleSecondaryNPrototype k ∈
      generatedFeasibleSecondaryLocalOrbit generatedFeasiblePhysicalRootPair := by
  fin_cases k
  · exact generatedFeasibleMate_axis_mem 0
  · exact generatedFeasibleMate_axis_mem 1
  · exact generatedFeasibleDisjointPair_axis_mem
      (0, generatedFeasibleDisjointPairPrototypeIndex) generatedFeasibleDisjointPairPrototype_mem 0
  · exact generatedFeasibleSecondaryNonPair_axis_mem 0 _
      generatedFeasibleContainingOctadPrototypeLabel_mem 0
  · exact generatedFeasibleSecondaryNonPair_axis_mem 1 _
      generatedFeasibleOutsideOctadPrototypeLabel_mem 0
  · exact generatedFeasibleSecondaryNonPair_axis_mem 2 _
      generatedFeasibleSecondaryOddPrototypeLabel_mem 0

private theorem inverse_transport
    (h : ↥(localAxisStabilizer generatedFeasiblePhysicalRootPair ⊓ localOmegaStabilizer))
    (x y : GriessSpace) (hh : rhoLocal h.val x = y) : rhoLocal h.val⁻¹ y = x := by
  rw [← hh, ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

/-- All original93150 secondary physical axes are covered by the actual six simultaneous orbits.
This is a classification for N; later classification under the first-axis group remains separate. -/
theorem generatedFeasibleSecondaryNOrbit_coverage (x : GriessSpace) :
    x ∈ generatedFeasibleOrthogonalSignedShortAxes ↔
      ∃ k : Fin 6, x ∈ generatedFeasibleSecondaryNOrbit k := by
  constructor
  · rintro ⟨z, rfl⟩
    have hr := (Finset.mem_product.mp z.property).1
    rcases (generatedFeasibleSecondary_catalogue_partition z.val.1).mp hr with
      ⟨pair, hp, he⟩ | ⟨k, hk⟩
    · change ∃ k : Fin 6, conwayShortAxis z.val.1 z.val.2 ∈ generatedFeasibleSecondaryNOrbit k
      rw [← he]
      rcases (generatedFeasibleDisjointPair_partition pair).mp hp with hm | hd
      · subst pair
        have hbinary : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide +kernel
        have hc := hbinary z.val.2
        rcases hc with hc | hc
        · refine ⟨0, ?_⟩
          change conwayShortAxis generatedFeasibleMateLabel z.val.2 ∈ generatedFeasibleMateOrbit 0
          rw [hc, generatedFeasibleMateOrbit_eq_singleton]
          exact Set.mem_singleton _
        · refine ⟨1, ?_⟩
          change conwayShortAxis generatedFeasibleMateLabel z.val.2 ∈ generatedFeasibleMateOrbit 1
          rw [hc, generatedFeasibleMateOrbit_eq_singleton]
          exact Set.mem_singleton _
      · obtain ⟨h, hh⟩ := generatedFeasibleDisjointPair_to_prototype pair hd z.val.2 0
        refine ⟨2, h⁻¹, ?_⟩
        exact inverse_transport h _ _ hh
    · fin_cases k
      · obtain ⟨h, hh⟩ := generatedFeasibleContainingOctad_to_prototype z.val.1 hk z.val.2 0
        refine ⟨3, h⁻¹, ?_⟩
        exact inverse_transport h _ _ hh
      · obtain ⟨h, hh⟩ := generatedFeasibleOutsideOctad_to_prototype z.val.1 hk z.val.2 0
        refine ⟨4, h⁻¹, ?_⟩
        exact inverse_transport h _ _ hh
      · obtain ⟨h, hh⟩ := generatedFeasibleSecondaryOdd_to_prototype z.val.1 hk z.val.2 0
        refine ⟨5, h⁻¹, ?_⟩
        exact inverse_transport h _ _ hh
  · rintro ⟨k, hk⟩
    rw [generatedFeasibleSecondaryNOrbit_eq] at hk
    obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp hk
    obtain ⟨a, ha⟩ := generatedFeasibleSecondaryNPrototype_mem k
    change rhoLocal a.val (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) =
      generatedFeasibleSecondaryNPrototype k at ha
    change rhoLocal h.val (generatedFeasibleSecondaryNPrototype k) = x at hh
    rw [← generatedFeasibleSecondaryLocalOrbit_eq_physical]
    refine ⟨⟨h.val, h.property.1⟩ * a, ?_⟩
    change rhoLocal (h.val * a.val) (generatedFeasibleSecondaryAxis
      generatedFeasiblePhysicalRootPair) = x
    rw [map_mul, LinearEquiv.mul_apply, ha]
    exact hh

/-- The six actual simultaneous orbit sizes sum to the entire original secondary catalogue. -/
theorem generatedFeasibleSecondaryNOrbit_size_total :
    (∑ k : Fin 6, Nat.card (generatedFeasibleSecondaryNOrbit k)) = 93150 := by
  simp_rw [generatedFeasibleSecondaryNOrbit_card]
  decide +kernel

/-- Apart from the two actual singletons, all displayed original orbit sizes are distinct. -/
private theorem orbitSize_equal_cases : ∀ k l : Fin 6,
    generatedFeasibleSecondaryNOrbitSize k = generatedFeasibleSecondaryNOrbitSize l →
      k = l ∨ (k = 0 ∧ l = 1) ∨ (k = 1 ∧ l = 0) := by
  decide +kernel

/-- The two genuine signed mate singleton orbits are unequal. -/
private theorem mate_orbits_ne : generatedFeasibleMateOrbit 0 ≠ generatedFeasibleMateOrbit 1 := by
  intro he
  have hm : conwayShortAxis generatedFeasibleMateLabel 0 ∈ generatedFeasibleMateOrbit 0 := by
    rw [generatedFeasibleMateOrbit_eq_singleton]
    exact Set.mem_singleton _
  rw [he, generatedFeasibleMateOrbit_eq_singleton] at hm
  have hh := @generatedAxis_signed_injective
    (generatedFeasibleMateLabel, 0) (generatedFeasibleMateLabel, 1)
      (Set.mem_singleton_iff.mp hm)
  have hc := congrArg (fun z : GriessShortIndex × ZMod 2 => z.2) hh
  exact (by decide : (0 : ZMod 2) ≠ 1) hc

/-- The six original displayed sectors are distinct actual simultaneous orbits. -/
theorem generatedFeasibleSecondaryNOrbit_injective :
    Function.Injective generatedFeasibleSecondaryNOrbit := by
  intro k l he
  have hc := congrArg (fun s : Set GriessSpace => Nat.card s) he
  rw [generatedFeasibleSecondaryNOrbit_card, generatedFeasibleSecondaryNOrbit_card] at hc
  rcases orbitSize_equal_cases k l hc with h | ⟨hk, hl⟩ | ⟨hk, hl⟩
  · exact h
  · subst k
    subst l
    exact False.elim (mate_orbits_ne he)
  · subst k
    subst l
    exact False.elim (mate_orbits_ne he.symm)

/-- The six actual simultaneous orbits are pairwise disjoint in the original Griess space. -/
theorem generatedFeasibleSecondaryNOrbit_pairwise_disjoint :
    Pairwise (fun k l : Fin 6 =>
      Disjoint (generatedFeasibleSecondaryNOrbit k) (generatedFeasibleSecondaryNOrbit l)) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro x hx hy
  rw [generatedFeasibleSecondaryNOrbit_eq] at hx hy
  have hm := MulAction.mem_orbit_trans (MulAction.mem_orbit_symm.mp hx) hy
  have he := MulAction.orbit_eq_iff.mpr hm
  rw [← generatedFeasibleSecondaryNOrbit_eq, ← generatedFeasibleSecondaryNOrbit_eq] at he
  exact hkl (generatedFeasibleSecondaryNOrbit_injective he)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
