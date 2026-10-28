/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveCatalogue
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageBinary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsCounts

/-! Global weighted reciprocity of actual triality transitions, and a counting criterion
for coverage of one family by the twelve-family catalogue.

The source singleton cocode element `s` exchanges triality and inverse triality, so
`x ↦ s (τ x)` is an involution of the Griess space. It carries the actual transitions from
the local orbit of `u` into the local orbit of `w` bijectively onto the actual transitions
from `w` into `u`. Hence the two vector transition counts agree for arbitrary vectors; with
the genuine coset/vector fiber equation this gives the coset form
`C(u → w) · |O_u| = C(w → u) · |O_w|`.

The counting criterion: lower bounds for the actual transition counts of one local orbit
into pairwise disjoint target orbits that add up to all 16,584,750 transition cosets (or to
the whole local orbit) force every triality transition of that orbit into the union of the
targets. A lower bound may come from either side of a pair through reciprocity. No source
table entry, prescribed orbit length or coverage statement is an input here. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem reciprocity_singleton_square (y : GriessSpace) :
    rhoLocal (inclQ singletonCocodeQ) (rhoLocal (inclQ singletonCocodeQ) y) = y := by
  have hs : inclQ singletonCocodeQ * inclQ singletonCocodeQ = (1 : H) := by
    rw [← map_mul]
    change inclQ (cocodeQ _ * cocodeQ _) = 1
    rw [cocodeQ_square, map_one]
  rw [← LinearEquiv.mul_apply, ← map_mul, hs, map_one, LinearEquiv.coe_one, id_eq]

/-- The singleton-reflected triality image `x ↦ s (τ x)`, for the source singleton `s`. -/
def generatedAxisGlobalTwelveReciprocityMap (x : GriessSpace) : GriessSpace :=
  rhoLocal (inclQ singletonCocodeQ) (sExtra x)

/-- Triality of the reflected image is the reflected original vector. -/
theorem generatedAxisGlobalTwelveReciprocityMap_triality (x : GriessSpace) :
    sExtra (generatedAxisGlobalTwelveReciprocityMap x) =
      rhoLocal (inclQ singletonCocodeQ) x := by
  rw [generatedAxisGlobalTwelveReciprocityMap, generatedAxisGlobal_singleton_triality_exchange,
    LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]

/-- The singleton-reflected triality image is an involution of the Griess space. -/
theorem generatedAxisGlobalTwelveReciprocityMap_involutive :
    Function.Involutive generatedAxisGlobalTwelveReciprocityMap := by
  intro x
  change rhoLocal (inclQ singletonCocodeQ)
    (sExtra (generatedAxisGlobalTwelveReciprocityMap x)) = x
  rw [generatedAxisGlobalTwelveReciprocityMap_triality, reciprocity_singleton_square]

/-- Points of the actual local orbit of `u` whose triality image lies in the actual local
orbit of `w`. -/
def generatedAxisGlobalTwelveTransitionSet (u w : GriessSpace) : Set GriessSpace :=
  {x | x ∈ MulAction.orbit H u ∧ sExtra x ∈ MulAction.orbit H w}

/-- The singleton reflection sends transitions from `u` to `w` to transitions from `w` to `u`. -/
theorem generatedAxisGlobalTwelveReciprocityMap_mapsTo (u w : GriessSpace) :
    Set.MapsTo generatedAxisGlobalTwelveReciprocityMap
      (generatedAxisGlobalTwelveTransitionSet u w)
      (generatedAxisGlobalTwelveTransitionSet w u) := by
  rintro x ⟨hu, hw⟩
  refine ⟨MulAction.mem_orbit_of_mem_orbit (inclQ singletonCocodeQ) hw, ?_⟩
  rw [generatedAxisGlobalTwelveReciprocityMap_triality]
  exact MulAction.mem_orbit_of_mem_orbit (inclQ singletonCocodeQ) hu

/-- The singleton reflection identifies the transitions from `u` to `w` with those from
`w` to `u`. -/
def generatedAxisGlobalTwelveTransitionSetEquiv (u w : GriessSpace) :
    generatedAxisGlobalTwelveTransitionSet u w ≃ generatedAxisGlobalTwelveTransitionSet w u where
  toFun x := ⟨_, generatedAxisGlobalTwelveReciprocityMap_mapsTo u w x.2⟩
  invFun y := ⟨_, generatedAxisGlobalTwelveReciprocityMap_mapsTo w u y.2⟩
  left_inv x := Subtype.ext (generatedAxisGlobalTwelveReciprocityMap_involutive x.1)
  right_inv y := Subtype.ext (generatedAxisGlobalTwelveReciprocityMap_involutive y.1)

/-- Global weighted reciprocity of actual triality transitions, for arbitrary vectors. -/
theorem generatedAxisGlobalTwelve_transition_reciprocity (u w : GriessSpace) :
    Nat.card (generatedAxisGlobalTwelveTransitionSet u w) =
      Nat.card (generatedAxisGlobalTwelveTransitionSet w u) :=
  Nat.card_congr (generatedAxisGlobalTwelveTransitionSetEquiv u w)

/-- Equality of actual local classes is membership in the actual local orbit. -/
theorem generatedAxisGlobalTwelve_class_eq_iff_mem_orbit (x w : GriessSpace) :
    Quotient.mk (MulAction.orbitRel H GriessSpace) x =
        Quotient.mk (MulAction.orbitRel H GriessSpace) w ↔
      x ∈ MulAction.orbit H w := by
  rw [Quotient.eq]
  exact MulAction.orbitRel_apply

/-- The existing actual axis fiber at the class of `w` is the transition set from `u` to `w`. -/
def generatedAxisGlobalTwelveAxisFiberEquiv (u w : GriessSpace) :
    generatedAxisGlobalTransitionAxisFiber u
        (Quotient.mk (MulAction.orbitRel H GriessSpace) w) ≃
      generatedAxisGlobalTwelveTransitionSet u w where
  toFun x := ⟨x.1.1, x.1.2, (generatedAxisGlobalTwelve_class_eq_iff_mem_orbit _ _).mp x.2⟩
  invFun y := ⟨⟨y.1, y.2.1⟩, (generatedAxisGlobalTwelve_class_eq_iff_mem_orbit _ _).mpr y.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Weighted reciprocity for the existing actual axis fibers. -/
theorem generatedAxisGlobalTwelve_axisFiber_reciprocity (u w : GriessSpace) :
    Nat.card (generatedAxisGlobalTransitionAxisFiber u
        (Quotient.mk (MulAction.orbitRel H GriessSpace) w)) =
      Nat.card (generatedAxisGlobalTransitionAxisFiber w
        (Quotient.mk (MulAction.orbitRel H GriessSpace) u)) := by
  rw [Nat.card_congr (generatedAxisGlobalTwelveAxisFiberEquiv u w),
    Nat.card_congr (generatedAxisGlobalTwelveAxisFiberEquiv w u)]
  exact generatedAxisGlobalTwelve_transition_reciprocity u w

private theorem reciprocity_stabilizer_mul_orbit (u : GriessSpace) :
    Nat.card (MulAction.stabilizer H u) * Nat.card (MulAction.orbit H u) = Nat.card H := by
  rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
  exact (MulAction.stabilizer H u).card_mul_index

/-- Weighted reciprocity of actual transition cosets:
`C(u → w) · |O_u| = C(w → u) · |O_w|`. -/
theorem generatedAxisGlobalTwelve_coset_reciprocity (u w : GriessSpace) :
    Nat.card (generatedAxisGlobalDestination u ⁻¹'
        {Quotient.mk (MulAction.orbitRel H GriessSpace) w}) * Nat.card (MulAction.orbit H u) =
      Nat.card (generatedAxisGlobalDestination w ⁻¹'
        {Quotient.mk (MulAction.orbitRel H GriessSpace) u}) * Nat.card (MulAction.orbit H w) := by
  have hb1 := generatedAxisGlobalTransition_fiber_balance u
    (Quotient.mk (MulAction.orbitRel H GriessSpace) w)
  have hb2 := generatedAxisGlobalTransition_fiber_balance w
    (Quotient.mk (MulAction.orbitRel H GriessSpace) u)
  have hr := generatedAxisGlobalTwelve_axisFiber_reciprocity u w
  have hu := reciprocity_stabilizer_mul_orbit u
  have hw := reciprocity_stabilizer_mul_orbit w
  have : Finite H := h_finite
  have hpos : 0 < Nat.card localOmegaStabilizer * Nat.card H :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  set A := Nat.card (generatedAxisGlobalDestination u ⁻¹'
    {Quotient.mk (MulAction.orbitRel H GriessSpace) w})
  set B := Nat.card (generatedAxisGlobalDestination w ⁻¹'
    {Quotient.mk (MulAction.orbitRel H GriessSpace) u})
  set N1 := Nat.card (generatedAxisGlobalTransitionAxisFiber u
    (Quotient.mk (MulAction.orbitRel H GriessSpace) w))
  set N2 := Nat.card (generatedAxisGlobalTransitionAxisFiber w
    (Quotient.mk (MulAction.orbitRel H GriessSpace) u))
  set om := Nat.card localOmegaStabilizer
  set su := Nat.card (MulAction.stabilizer H u)
  set sw := Nat.card (MulAction.stabilizer H w)
  set ou := Nat.card (MulAction.orbit H u)
  set ow := Nat.card (MulAction.orbit H w)
  set hh := Nat.card H
  calc A * ou * (om * hh) = (A * om) * (ou * hh) := by ring
    _ = (N1 * su) * (ou * hh) := by rw [hb1]
    _ = N1 * (su * ou) * hh := by ring
    _ = N1 * hh * hh := by rw [hu]
    _ = N2 * hh * hh := by rw [hr]
    _ = N2 * (sw * ow) * hh := by rw [hw]
    _ = (N2 * sw) * (ow * hh) := by ring
    _ = (B * om) * (ow * hh) := by rw [hb2]
    _ = B * ow * (om * hh) := by ring

private theorem reciprocity_orbit_card_pos (u : GriessSpace) :
    0 < Nat.card (MulAction.orbit H u) := by
  have : Finite H := h_finite
  have : Finite (MulAction.orbit H u) := Set.finite_range _ |>.to_subtype
  have : Nonempty (MulAction.orbit H u) := ⟨⟨u, MulAction.mem_orbit_self u⟩⟩
  exact Nat.card_pos

/-- A lower bound for the reverse transition coset count transfers through reciprocity,
scaled by the two actual local orbit lengths. -/
theorem generatedAxisGlobalTwelve_coset_lower_bound_of_reverse {u w : GriessSpace} {t t' : ℕ}
    (ht' : t' ≤ Nat.card (generatedAxisGlobalDestination w ⁻¹'
      {Quotient.mk (MulAction.orbitRel H GriessSpace) u}))
    (hscale : t * Nat.card (MulAction.orbit H u) = t' * Nat.card (MulAction.orbit H w)) :
    t ≤ Nat.card (generatedAxisGlobalDestination u ⁻¹'
      {Quotient.mk (MulAction.orbitRel H GriessSpace) w}) := by
  apply Nat.le_of_mul_le_mul_right _ (reciprocity_orbit_card_pos u)
  rw [hscale, generatedAxisGlobalTwelve_coset_reciprocity u w]
  exact Nat.mul_le_mul_right _ ht'

/-- A set of transition cosets with the destination class of `w` bounds the coset count. -/
theorem generatedAxisGlobalTwelve_coset_lower_bound_of_subset {u w : GriessSpace}
    (S : Set generatedAxisTransitionCosetSpace)
    (hS : ∀ c ∈ S, generatedAxisGlobalDestination u c =
      Quotient.mk (MulAction.orbitRel H GriessSpace) w) :
    Nat.card S ≤ Nat.card (generatedAxisGlobalDestination u ⁻¹'
      {Quotient.mk (MulAction.orbitRel H GriessSpace) w}) := by
  have : Finite generatedAxisTransitionCosetSpace := by
    apply Nat.finite_of_card_ne_zero
    rw [generatedAxisTransitionCosetSpace_card]
    decide
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  exact Set.ncard_le_ncard hS

private theorem reciprocity_class_ne {ι : Type*} (w : ι → GriessSpace)
    (hdisj : Pairwise fun j k => Disjoint (MulAction.orbit H (w j)) (MulAction.orbit H (w k)))
    {j k : ι} (hjk : j ≠ k) :
    Quotient.mk (MulAction.orbitRel H GriessSpace) (w j) ≠
      Quotient.mk (MulAction.orbitRel H GriessSpace) (w k) := by
  intro he
  have hm := (generatedAxisGlobalTwelve_class_eq_iff_mem_orbit _ _).mp he
  exact Set.disjoint_left.mp (hdisj hjk) (MulAction.mem_orbit_self (w j)) hm

/-- Counting criterion on transition cosets: lower bounds for the actual coset counts into
pairwise disjoint local orbits, adding up to all transition cosets, force every triality
transition of the local orbit of `u` into the union of those orbits. -/
theorem generatedAxisGlobalTwelve_mem_union_of_coset_lower_bounds {ι : Type*} [Fintype ι]
    (w : ι → GriessSpace) (u : GriessSpace)
    (hdisj : Pairwise fun j k => Disjoint (MulAction.orbit H (w j)) (MulAction.orbit H (w k)))
    (t : ι → ℕ)
    (ht : ∀ j, t j ≤ Nat.card (generatedAxisGlobalDestination u ⁻¹'
      {Quotient.mk (MulAction.orbitRel H GriessSpace) (w j)}))
    (hsum : ∑ j, t j = 16584750) (h : H) :
    sExtra (rhoLocal h u) ∈ generatedLocalOrbitUnion w := by
  have : Finite generatedAxisTransitionCosetSpace := by
    apply Nat.finite_of_card_ne_zero
    rw [generatedAxisTransitionCosetSpace_card]
    decide
  let P : ι → Set generatedAxisTransitionCosetSpace := fun j =>
    generatedAxisGlobalDestination u ⁻¹' {Quotient.mk (MulAction.orbitRel H GriessSpace) (w j)}
  have hP : Pairwise fun j k => Disjoint (P j) (P k) := by
    intro j k hjk
    refine Set.disjoint_left.mpr ?_
    intro c hj hk
    exact reciprocity_class_ne w hdisj hjk ((Set.mem_singleton_iff.mp hj).symm.trans
      (Set.mem_singleton_iff.mp hk))
  have hcard : Nat.card (⋃ j, P j) = ∑ j, Nat.card (P j) := by
    rw [Nat.card_congr (Set.unionEqSigmaOfDisjoint hP), Nat.card_sigma]
  have hge : (Set.univ : Set generatedAxisTransitionCosetSpace).ncard ≤ (⋃ j, P j).ncard := by
    rw [Set.ncard_univ, generatedAxisTransitionCosetSpace_card, ← Nat.card_coe_set_eq, hcard,
      ← hsum]
    exact Finset.sum_le_sum fun j _ => ht j
  have huniv := Set.eq_of_subset_of_ncard_le (Set.subset_univ _) hge
  have hc : Quotient.mk (QuotientGroup.rightRel localOmegaStabilizer) h ∈ ⋃ j, P j := by
    rw [huniv]
    exact Set.mem_univ _
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hc
  exact (generatedAxisGlobal_mem_union_iff w _).mpr ⟨j, Set.mem_singleton_iff.mp hj⟩

/-- Counting criterion on local orbit points: lower bounds for the actual vector transition
counts into pairwise disjoint local orbits, adding up to the length of the local orbit of `u`,
force every triality transition of that orbit into the union of those orbits. -/
theorem generatedAxisGlobalTwelve_mem_union_of_axis_lower_bounds {ι : Type*} [Fintype ι]
    (w : ι → GriessSpace) (u : GriessSpace)
    (hdisj : Pairwise fun j k => Disjoint (MulAction.orbit H (w j)) (MulAction.orbit H (w k)))
    (t : ι → ℕ)
    (ht : ∀ j, t j ≤ Nat.card (generatedAxisGlobalTwelveTransitionSet u (w j)))
    (hsum : ∑ j, t j = Nat.card (MulAction.orbit H u)) (h : H) :
    sExtra (rhoLocal h u) ∈ generatedLocalOrbitUnion w := by
  have : Finite H := h_finite
  have hfin : (MulAction.orbit H u).Finite := Set.finite_range _
  let T : ι → Set GriessSpace := fun j => generatedAxisGlobalTwelveTransitionSet u (w j)
  have hTsub : (⋃ j, T j) ⊆ MulAction.orbit H u :=
    Set.iUnion_subset fun j _ hx => hx.1
  have hTfin (j : ι) : Finite (T j) :=
    (hfin.subset fun _ hx => hx.1).to_subtype
  have hT : Pairwise fun j k => Disjoint (T j) (T k) := by
    intro j k hjk
    refine Set.disjoint_left.mpr ?_
    intro x hj hk
    exact Set.disjoint_left.mp (hdisj hjk) hj.2 hk.2
  have hcard : Nat.card (⋃ j, T j) = ∑ j, Nat.card (T j) := by
    rw [Nat.card_congr (Set.unionEqSigmaOfDisjoint hT), Nat.card_sigma]
  have hge : (MulAction.orbit H u).ncard ≤ (⋃ j, T j).ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hcard, ← hsum]
    exact Finset.sum_le_sum fun j _ => ht j
  have heq := Set.eq_of_subset_of_ncard_le hTsub hge hfin
  have hx : rhoLocal h u ∈ ⋃ j, T j := by
    rw [heq]
    exact ⟨h, rfl⟩
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  obtain ⟨k, hk⟩ := hj.2
  exact ⟨j, k, hk⟩

/-- Coset counting criterion for one listed family of the twelve-family catalogue. -/
theorem generatedAxisGlobalTwelve_familyCovered_of_coset_lower_bounds
    (hdisj : Pairwise fun j k => Disjoint (generatedAxisGlobalTwelveOrbit j)
      (generatedAxisGlobalTwelveOrbit k))
    (i : Fin 12) (t : Fin 12 → ℕ)
    (ht : ∀ j, t j ≤ Nat.card (generatedAxisGlobalDestination
      (generatedAxisGlobalTwelveRepresentative i) ⁻¹'
        {Quotient.mk (MulAction.orbitRel H GriessSpace)
          (generatedAxisGlobalTwelveRepresentative j)}))
    (hsum : ∑ j, t j = 16584750) :
    GeneratedAxisGlobalTwelveFamilyCovered i := fun h =>
  generatedAxisGlobalTwelve_mem_union_of_coset_lower_bounds _ _ hdisj t ht hsum h

/-- Vector counting criterion for one listed family of the twelve-family catalogue. -/
theorem generatedAxisGlobalTwelve_familyCovered_of_axis_lower_bounds
    (hdisj : Pairwise fun j k => Disjoint (generatedAxisGlobalTwelveOrbit j)
      (generatedAxisGlobalTwelveOrbit k))
    (i : Fin 12) (t : Fin 12 → ℕ)
    (ht : ∀ j, t j ≤ Nat.card (generatedAxisGlobalTwelveTransitionSet
      (generatedAxisGlobalTwelveRepresentative i) (generatedAxisGlobalTwelveRepresentative j)))
    (hsum : ∑ j, t j = Nat.card (generatedAxisGlobalTwelveOrbit i)) :
    GeneratedAxisGlobalTwelveFamilyCovered i := fun h =>
  generatedAxisGlobalTwelve_mem_union_of_axis_lower_bounds _ _ hdisj t ht hsum h

/-- Exact twelve local lengths supply the disjointness input of both counting criteria. -/
theorem generatedAxisGlobalTwelve_familyCovered_of_counted_coset_lower_bounds
    (hc : GeneratedAxisGlobalTwelveCounted) (i : Fin 12) (t : Fin 12 → ℕ)
    (ht : ∀ j, t j ≤ Nat.card (generatedAxisGlobalDestination
      (generatedAxisGlobalTwelveRepresentative i) ⁻¹'
        {Quotient.mk (MulAction.orbitRel H GriessSpace)
          (generatedAxisGlobalTwelveRepresentative j)}))
    (hsum : ∑ j, t j = 16584750) :
    GeneratedAxisGlobalTwelveFamilyCovered i :=
  generatedAxisGlobalTwelve_familyCovered_of_coset_lower_bounds
    (generatedAxisGlobalTwelveOrbit_pairwise_disjoint hc) i t ht hsum

/-- Reverse coset lower bound between two listed families, scaled by the catalogue lengths. -/
theorem generatedAxisGlobalTwelve_coset_lower_bound_of_reverse_counted
    (hc : GeneratedAxisGlobalTwelveCounted) {i j : Fin 12} {t t' : ℕ}
    (ht' : t' ≤ Nat.card (generatedAxisGlobalDestination
      (generatedAxisGlobalTwelveRepresentative j) ⁻¹'
        {Quotient.mk (MulAction.orbitRel H GriessSpace)
          (generatedAxisGlobalTwelveRepresentative i)}))
    (hscale : t * generatedAxisGlobalTwelveCount i = t' * generatedAxisGlobalTwelveCount j) :
    t ≤ Nat.card (generatedAxisGlobalDestination
      (generatedAxisGlobalTwelveRepresentative i) ⁻¹'
        {Quotient.mk (MulAction.orbitRel H GriessSpace)
          (generatedAxisGlobalTwelveRepresentative j)}) := by
  apply generatedAxisGlobalTwelve_coset_lower_bound_of_reverse ht'
  have hi := hc i
  have hj := hc j
  rw [generatedAxisGlobalTwelveOrbit] at hi hj
  rw [hi, hj]
  exact hscale

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
