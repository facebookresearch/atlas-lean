/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsoradialCellularRibbonDuality











namespace StatMech.FrontierA

open Matrix Finset
open scoped BigOperators

variable {V E D : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]



noncomputable def finiteTwistedLaplacian
    (conductance transport : V -> V -> Complex) : Matrix V V Complex :=
  fun v w => if v = w then ∑ u, conductance v u
    else -conductance v w * transport v w




theorem det_finiteTwistedLaplacian_permutation
    (conductance transport : V -> V -> Complex) :
    (finiteTwistedLaplacian conductance transport).det =
      ∑ sigma : Equiv.Perm V,
        Equiv.Perm.sign sigma •
          ∏ v : V,
            if sigma v = v then ∑ u, conductance (sigma v) u
            else -conductance (sigma v) v * transport (sigma v) v := by
  rw [Matrix.det_apply]
  simp [finiteTwistedLaplacian]



abbrev laplacianPermutationFixedPoint (sigma : Equiv.Perm V) :=
  {v : V // sigma v = v}

instance laplacianPermutationFixedPointFintype (sigma : Equiv.Perm V) :
    Fintype (laplacianPermutationFixedPoint sigma) :=
  Fintype.subtype (Finset.univ.filter fun v => sigma v = v) (by simp)




def finiteCRSFWitness (V : Type*) [Fintype V] [DecidableEq V] :=
  Σ sigma : Equiv.Perm V, laplacianPermutationFixedPoint sigma -> V

noncomputable instance finiteCRSFWitnessFintype
    (V : Type*) [Fintype V] [DecidableEq V] :
    Fintype (finiteCRSFWitness V) := by
  unfold finiteCRSFWitness laplacianPermutationFixedPoint
  infer_instance




noncomputable def finiteCRSFWitnessNext (X : finiteCRSFWitness V) : V -> V :=
  fun v => if h : X.1 v = v then X.2 ⟨v, h⟩ else X.1.symm v

@[simp] theorem finiteCRSFWitnessNext_fixed
    (X : finiteCRSFWitness V) (v : V) (hv : X.1 v = v) :
    finiteCRSFWitnessNext X v = X.2 ⟨v, hv⟩ := by
  simp [finiteCRSFWitnessNext, hv]

theorem finiteCRSFWitnessNext_nonfixed_cycle
    (X : finiteCRSFWitness V) (v : V) (hv : X.1 v ≠ v) :
    finiteCRSFWitnessNext X (X.1 v) = v := by
  have hnonfixed : X.1 (X.1 v) ≠ X.1 v := by
    intro h
    exact hv (X.1.injective h)
  simp [finiteCRSFWitnessNext, hnonfixed]



theorem finiteCRSFWitnessNext_injectiveOn_support
    (X : finiteCRSFWitness V) :
    Set.InjOn (finiteCRSFWitnessNext X) X.1.support := by
  intro a ha b hb hab
  have ha' : X.1 a ≠ a := Equiv.Perm.mem_support.mp ha
  have hb' : X.1 b ≠ b := Equiv.Perm.mem_support.mp hb
  have hab' : X.1.symm a = X.1.symm b := by
    simpa only [finiteCRSFWitnessNext, dif_neg ha', dif_neg hb'] using hab
  exact X.1.symm.injective hab'


noncomputable def finiteCRSFWitnessTerm
    (conductance transport : V -> V -> Complex)
    (X : finiteCRSFWitness V) : Complex :=
  Equiv.Perm.sign X.1 •
    ((∏ v : laplacianPermutationFixedPoint X.1,
        conductance v (X.2 v)) *
      ∏ v ∈ (Finset.univ.filter fun v => X.1 v ≠ v),
        -conductance (X.1 v) v * transport (X.1 v) v)



theorem det_finiteTwistedLaplacian_eq_sum_finiteCRSFWitness
    (conductance transport : V -> V -> Complex) :
    (finiteTwistedLaplacian conductance transport).det =
      ∑ X : finiteCRSFWitness V,
        finiteCRSFWitnessTerm conductance transport X := by
  rw [det_finiteTwistedLaplacian_permutation]
  have hSigma :
      (∑ X : finiteCRSFWitness V,
          finiteCRSFWitnessTerm conductance transport X) =
        ∑ sigma : Equiv.Perm V,
          ∑ target : laplacianPermutationFixedPoint sigma -> V,
            finiteCRSFWitnessTerm conductance transport
              ⟨sigma, target⟩ := by
    exact Fintype.sum_sigma _
  rw [hSigma]
  apply Finset.sum_congr rfl
  intro sigma _
  let fixed : Finset V := Finset.univ.filter fun v => sigma v = v
  have hsplit :
      (∏ v : V,
          if sigma v = v then ∑ u, conductance (sigma v) u
          else -conductance (sigma v) v * transport (sigma v) v) =
        (∏ v ∈ fixed, ∑ u, conductance (sigma v) u) *
          ∏ v ∈ (Finset.univ.filter fun v => sigma v ≠ v),
            -conductance (sigma v) v * transport (sigma v) v := by
    simpa [fixed] using
      (Finset.prod_ite
        (s := (Finset.univ : Finset V))
        (p := fun v => sigma v = v)
        (fun v => ∑ u, conductance (sigma v) u)
        (fun v => -conductance (sigma v) v * transport (sigma v) v))
  have hfixed :
      (∏ v ∈ fixed, ∑ u, conductance (sigma v) u) =
        ∑ target : laplacianPermutationFixedPoint sigma -> V,
          ∏ v : laplacianPermutationFixedPoint sigma,
            conductance v (target v) := by
    calc
      (∏ v ∈ fixed, ∑ u, conductance (sigma v) u) =
          ∏ v : laplacianPermutationFixedPoint sigma,
            ∑ u, conductance (sigma v) u := by
        apply Finset.prod_subtype fixed
        · intro v
          simp [fixed]
      _ = ∏ v : laplacianPermutationFixedPoint sigma,
            ∑ u, conductance v u := by
        apply Finset.prod_congr rfl
        intro v _
        rw [v.property]
      _ = ∑ target : laplacianPermutationFixedPoint sigma -> V,
          ∏ v : laplacianPermutationFixedPoint sigma,
            conductance v (target v) := by
        simpa using
          (Fintype.prod_sum
            (fun (v : laplacianPermutationFixedPoint sigma) (u : V) =>
              conductance v u))
  rw [hsplit, hfixed, Finset.sum_mul, smul_sum]
  apply Finset.sum_congr rfl
  intro target _
  rfl


abbrev finiteCRSFWitnessFiber (next : V -> V) :=
  {X : finiteCRSFWitness V // finiteCRSFWitnessNext X = next}

noncomputable instance finiteCRSFWitnessFiberFintype (next : V -> V) :
    Fintype (finiteCRSFWitnessFiber next) :=
  Fintype.subtype
    (Finset.univ.filter fun X : finiteCRSFWitness V =>
      finiteCRSFWitnessNext X = next) (by simp)



structure finiteCRSFCycleSupport (next : V -> V) where
  carrier : Finset V
  mapsTo : forall v, v ∈ carrier -> next v ∈ carrier
  injOn : Set.InjOn next carrier
  noFixed : forall v, v ∈ carrier -> next v ≠ v



def finiteCRSFAtomicCycle (next : V -> V) :=
  {cycle : Equiv.Perm V // cycle.IsCycle ∧
    ∀ v ∈ cycle.support, cycle v = next v}

noncomputable instance finiteCRSFAtomicCycleFintype (next : V -> V) :
    Fintype (finiteCRSFAtomicCycle next) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter fun cycle : Equiv.Perm V =>
      cycle.IsCycle ∧ ∀ v ∈ cycle.support, cycle v = next v) (by
        intro cycle
        simp)



theorem finiteCRSFAtomicCycle_support_disjoint {next : V -> V}
    {cycle cycle' : finiteCRSFAtomicCycle next} (hne : cycle ≠ cycle') :
    Disjoint cycle.1.support cycle'.1.support := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  apply hne
  apply Subtype.ext
  apply cycle.2.1.eq_on_support_inter_nonempty_congr cycle'.2.1
  · intro w hw
    have hw' := Finset.mem_inter.mp hw
    exact (cycle.2.2 w hw'.1).trans (cycle'.2.2 w hw'.2).symm
  · exact (cycle.2.2 v hv).trans (cycle'.2.2 v hv').symm
  · exact hv


noncomputable def finiteCRSFAtomicCycle.holonomy {next : V -> V}
    (transport : V -> V -> Complex)
    (cycle : finiteCRSFAtomicCycle next) : Complex :=
  ∏ v ∈ cycle.1.support, transport v (next v)

namespace finiteCRSFCycleSupport

omit [Fintype V] [DecidableEq V] in
@[ext]
theorem ext {next : V -> V}
    {S T : finiteCRSFCycleSupport next}
    (hcarrier : S.carrier = T.carrier) : S = T := by
  cases S
  cases T
  cases hcarrier
  rfl




noncomputable def ofAtomicCycles {next : V -> V}
    (selected : Finset (finiteCRSFAtomicCycle next)) :
    finiteCRSFCycleSupport next where
  carrier := selected.biUnion fun cycle => cycle.1.support
  mapsTo := by
    intro v hv
    rw [Finset.mem_biUnion] at hv ⊢
    rcases hv with ⟨cycle, hcycle, hv⟩
    refine ⟨cycle, hcycle, ?_⟩
    rw [← cycle.2.2 v hv]
    exact Equiv.Perm.apply_mem_support.mpr hv
  injOn := by
    intro a ha b hb hab
    change a ∈ selected.biUnion (fun cycle => cycle.1.support) at ha
    change b ∈ selected.biUnion (fun cycle => cycle.1.support) at hb
    rw [Finset.mem_biUnion] at ha hb
    rcases ha with ⟨cycle, hcycle, ha⟩
    rcases hb with ⟨cycle', hcycle', hb⟩
    have hca : cycle.1 a = next a := cycle.2.2 a ha
    have hcb : cycle'.1 b = next b := cycle'.2.2 b hb
    have hnexta : next a ∈ cycle.1.support := by
      rw [← hca]
      exact Equiv.Perm.apply_mem_support.mpr ha
    have hnextb : next b ∈ cycle'.1.support := by
      rw [← hcb]
      exact Equiv.Perm.apply_mem_support.mpr hb
    have hcycles : cycle = cycle' := by
      by_contra hne
      have hdisjoint := finiteCRSFAtomicCycle_support_disjoint hne
      exact (Finset.disjoint_left.mp hdisjoint hnexta) (by
        rw [hab]
        exact hnextb)
    subst cycle'
    apply cycle.1.injective
    rw [hca, hcb, hab]
  noFixed := by
    intro v hv
    rw [Finset.mem_biUnion] at hv
    rcases hv with ⟨cycle, _hcycle, hv⟩
    intro hnext
    exact (Equiv.Perm.mem_support.mp hv)
      ((cycle.2.2 v hv).trans hnext)


noncomputable def restrictedPerm {next : V -> V}
    (S : finiteCRSFCycleSupport next) : Equiv.Perm (↑S.carrier) := by
  let f : ↑S.carrier -> ↑S.carrier :=
    fun v => ⟨next v, S.mapsTo v v.property⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact S.injOn a.property b.property (congrArg Subtype.val hab)
  exact Equiv.ofBijective f
    ⟨hinj, (Finite.injective_iff_surjective.mp hinj)⟩


noncomputable def ambientPerm {next : V -> V}
    (S : finiteCRSFCycleSupport next) : Equiv.Perm V :=
  Equiv.Perm.ofSubtype S.restrictedPerm.symm

theorem ambientPerm_apply_of_mem {next : V -> V}
    (S : finiteCRSFCycleSupport next) {v : V} (hv : v ∈ S.carrier) :
    S.ambientPerm v = S.restrictedPerm.symm ⟨v, hv⟩ := by
  exact Equiv.Perm.ofSubtype_apply_of_mem _ hv

theorem ambientPerm_apply_of_not_mem {next : V -> V}
    (S : finiteCRSFCycleSupport next) {v : V} (hv : v ∉ S.carrier) :
    S.ambientPerm v = v := by
  exact Equiv.Perm.ofSubtype_apply_of_not_mem _ hv

theorem ambientPerm_symm_apply_of_mem {next : V -> V}
    (S : finiteCRSFCycleSupport next) {v : V} (hv : v ∈ S.carrier) :
    S.ambientPerm.symm v = next v := by
  have hinv : S.ambientPerm.symm =
      Equiv.Perm.ofSubtype S.restrictedPerm := by
    change (Equiv.Perm.ofSubtype S.restrictedPerm.symm)⁻¹ = _
    rw [← map_inv]
    rfl
  rw [hinv, Equiv.Perm.ofSubtype_apply_of_mem _ hv]
  rfl

theorem ambientPerm_ne_of_mem {next : V -> V}
    (S : finiteCRSFCycleSupport next) {v : V} (hv : v ∈ S.carrier) :
    S.ambientPerm v ≠ v := by
  intro hfixed
  have hs : S.ambientPerm.symm v = v := by
    calc
      S.ambientPerm.symm v =
          S.ambientPerm.symm (S.ambientPerm v) :=
        congrArg S.ambientPerm.symm hfixed.symm
      _ = v := S.ambientPerm.symm_apply_apply v
  rw [S.ambientPerm_symm_apply_of_mem hv] at hs
  exact S.noFixed v hv hs


theorem ambientPerm_support {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    S.ambientPerm.support = S.carrier := by
  ext v
  rw [Equiv.Perm.mem_support]
  constructor
  · intro hmove
    by_contra hv
    exact hmove (S.ambientPerm_apply_of_not_mem hv)
  · exact S.ambientPerm_ne_of_mem


noncomputable def toWitness {next : V -> V}
    (S : finiteCRSFCycleSupport next) : finiteCRSFWitness V :=
  ⟨S.ambientPerm, fun v => next v⟩

theorem next_toWitness {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    finiteCRSFWitnessNext S.toWitness = next := by
  funext v
  by_cases hv : v ∈ S.carrier
  · have hne := S.ambientPerm_ne_of_mem hv
    change (if h : S.ambientPerm v = v then next v
      else S.ambientPerm.symm v) = next v
    rw [dif_neg hne]
    exact S.ambientPerm_symm_apply_of_mem hv
  · have heq := S.ambientPerm_apply_of_not_mem hv
    change (if h : S.ambientPerm v = v then next v
      else S.ambientPerm.symm v) = next v
    rw [dif_pos heq]



noncomputable def toFiber {next : V -> V}
    (S : finiteCRSFCycleSupport next) : finiteCRSFWitnessFiber next :=
  ⟨S.toWitness, S.next_toWitness⟩



noncomputable def term {next : V -> V}
    (conductance transport : V -> V -> Complex)
    (S : finiteCRSFCycleSupport next) : Complex :=
  Equiv.Perm.sign S.ambientPerm •
    ((∏ v ∈ (Finset.univ.filter fun v => v ∉ S.carrier),
        conductance v (next v)) *
      ∏ v ∈ S.carrier,
        -conductance v (next v) * transport v (next v))



theorem restrictedPerm_support {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    S.restrictedPerm.support = Finset.univ := by
  ext v
  simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
  intro hfixed
  have hnext : next v = v := by
    exact congrArg Subtype.val hfixed
  exact S.noFixed v v.property hnext


noncomputable def atomicCycles {next : V -> V}
    (S : finiteCRSFCycleSupport next) : Finset (Equiv.Perm (↑S.carrier)) :=
  S.restrictedPerm.cycleFactorsFinset

theorem mem_atomicCycles_isCycle {next : V -> V}
    (S : finiteCRSFCycleSupport next) {cycle : Equiv.Perm (↑S.carrier)}
    (hcycle : cycle ∈ S.atomicCycles) : cycle.IsCycle :=
  (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hcycle).1


theorem exists_mem_atomicCycle {next : V -> V}
    (S : finiteCRSFCycleSupport next) (v : ↑S.carrier) :
    ∃ cycle ∈ S.atomicCycles, v ∈ cycle.support := by
  change ∃ cycle ∈ S.restrictedPerm.cycleFactorsFinset,
    v ∈ cycle.support
  rw [← Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset,
    S.restrictedPerm_support]
  simp



theorem atomicCycle_apply {next : V -> V}
    (S : finiteCRSFCycleSupport next) {cycle : Equiv.Perm (↑S.carrier)}
    (hcycle : cycle ∈ S.atomicCycles) (v : ↑S.carrier)
    (hv : v ∈ cycle.support) : (cycle v : V) = next v := by
  have hrestrict := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hcycle).2 v hv
  exact congrArg Subtype.val hrestrict


noncomputable def toAtomicCycle {next : V -> V}
    (S : finiteCRSFCycleSupport next)
    (cycle : {cycle // cycle ∈ S.atomicCycles}) :
    finiteCRSFAtomicCycle next := by
  refine ⟨Equiv.Perm.ofSubtype cycle.1, ?_, ?_⟩
  · change (cycle.1.extendDomain (Equiv.refl (↑S.carrier))).IsCycle
    exact (S.mem_atomicCycles_isCycle cycle.2).extendDomain _
  · intro v hv
    have hvcarrier : v ∈ S.carrier := by
      by_contra hcarrier
      exact (Equiv.Perm.mem_support.mp hv)
        (Equiv.Perm.ofSubtype_apply_of_not_mem _ hcarrier)
    let w : ↑S.carrier := ⟨v, hvcarrier⟩
    have hw : w ∈ cycle.1.support := by
      rw [Equiv.Perm.mem_support]
      intro hfixed
      apply Equiv.Perm.mem_support.mp hv
      rw [Equiv.Perm.ofSubtype_apply_of_mem _ hvcarrier]
      exact congrArg Subtype.val hfixed
    rw [Equiv.Perm.ofSubtype_apply_of_mem _ hvcarrier]
    exact S.atomicCycle_apply cycle.2 w hw

noncomputable def atomicCycleEmbedding {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    {cycle // cycle ∈ S.atomicCycles} ↪ finiteCRSFAtomicCycle next where
  toFun := S.toAtomicCycle
  inj' := by
    intro cycle cycle' h
    apply Subtype.ext
    exact Equiv.Perm.ofSubtype_injective (congrArg Subtype.val h)


noncomputable def toAtomicCycles {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    Finset (finiteCRSFAtomicCycle next) :=
  Finset.univ.map S.atomicCycleEmbedding

theorem mem_toAtomicCycles_support_subset {next : V -> V}
    (S : finiteCRSFCycleSupport next) {cycle : finiteCRSFAtomicCycle next}
    (hcycle : cycle ∈ S.toAtomicCycles) :
    cycle.1.support ⊆ S.carrier := by
  rw [toAtomicCycles, Finset.mem_map] at hcycle
  rcases hcycle with ⟨cycle', _huniv, rfl⟩
  intro v hv
  change v ∈ (Equiv.Perm.ofSubtype cycle'.1).support at hv
  rw [Equiv.Perm.support_ofSubtype] at hv
  rcases Finset.mem_map.mp hv with ⟨w, _hw, rfl⟩
  exact w.property

theorem mem_toAtomicCycles_iff_support_subset {next : V -> V}
    (S : finiteCRSFCycleSupport next) (cycle : finiteCRSFAtomicCycle next) :
    cycle ∈ S.toAtomicCycles ↔ cycle.1.support ⊆ S.carrier := by
  constructor
  · exact S.mem_toAtomicCycles_support_subset
  · intro hsubset
    have hinvariant (v : V) :
        cycle.1 v ∈ S.carrier ↔ v ∈ S.carrier := by
      constructor
      · intro hv
        by_cases hfixed : cycle.1 v = v
        · simpa [hfixed] using hv
        · exact hsubset (Equiv.Perm.mem_support.mpr hfixed)
      · intro hv
        by_cases hfixed : cycle.1 v = v
        · simpa [hfixed] using hv
        · rw [cycle.2.2 v (Equiv.Perm.mem_support.mpr hfixed)]
          exact S.mapsTo v hv
    let restricted : Equiv.Perm (↑S.carrier) :=
      cycle.1.subtypePerm hinvariant
    have hrestrictedCycle : restricted.IsCycle := by
      obtain ⟨v, hv⟩ := cycle.2.1.nonempty_support
      let w : ↑S.carrier := ⟨v, hsubset hv⟩
      refine ⟨w, ?_, ?_⟩
      · intro hfixed
        apply Equiv.Perm.mem_support.mp hv
        have hval := congrArg Subtype.val hfixed
        simpa [restricted, w] using hval
      · intro w' hw'
        have hwAmbient : cycle.1 (w' : V) ≠ w' := by
          intro hfixed
          apply hw'
          apply Subtype.ext
          exact hfixed
        exact (cycle.2.1.sameCycle
          (Equiv.Perm.mem_support.mp hv) hwAmbient).subtypePerm
    have hfactor : restricted ∈ S.atomicCycles := by
      rw [atomicCycles, Equiv.Perm.mem_cycleFactorsFinset_iff]
      refine ⟨hrestrictedCycle, ?_⟩
      intro v hv
      apply Subtype.ext
      have hvAmbient : (v : V) ∈ cycle.1.support := by
        rw [Equiv.Perm.mem_support]
        intro hfixed
        apply Equiv.Perm.mem_support.mp hv
        apply Subtype.ext
        exact hfixed
      calc
        (restricted v : V) = cycle.1 v := rfl
        _ = next v := cycle.2.2 v hvAmbient
        _ = (S.restrictedPerm v : V) := rfl
    rw [toAtomicCycles, Finset.mem_map]
    refine ⟨⟨restricted, hfactor⟩, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    change Equiv.Perm.ofSubtype restricted = cycle.1
    exact Equiv.Perm.ofSubtype_subtypePerm hinvariant
      (fun v hv => hsubset (Equiv.Perm.mem_support.mpr hv))

theorem carrier_ofAtomicCycles_toAtomicCycles {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    (ofAtomicCycles S.toAtomicCycles).carrier = S.carrier := by
  ext v
  constructor
  · intro hv
    change v ∈ S.toAtomicCycles.biUnion
      (fun cycle => cycle.1.support) at hv
    rw [Finset.mem_biUnion] at hv
    rcases hv with ⟨cycle, hcycle, hv⟩
    exact S.mem_toAtomicCycles_support_subset hcycle hv
  · intro hv
    obtain ⟨cycle, hcycle, hvcycle⟩ :=
      S.exists_mem_atomicCycle ⟨v, hv⟩
    change v ∈ S.toAtomicCycles.biUnion
      (fun cycle => cycle.1.support)
    rw [Finset.mem_biUnion]
    refine ⟨S.toAtomicCycle ⟨cycle, hcycle⟩, ?_, ?_⟩
    · rw [toAtomicCycles, Finset.mem_map]
      exact ⟨⟨cycle, hcycle⟩, Finset.mem_univ _, rfl⟩
    · change v ∈ (Equiv.Perm.ofSubtype cycle).support
      rw [Equiv.Perm.mem_support,
        Equiv.Perm.ofSubtype_apply_of_mem _ hv]
      intro hfixed
      exact (Equiv.Perm.mem_support.mp hvcycle) (Subtype.ext hfixed)

theorem ofAtomicCycles_toAtomicCycles {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    ofAtomicCycles S.toAtomicCycles = S := by
  apply finiteCRSFCycleSupport.ext
  exact S.carrier_ofAtomicCycles_toAtomicCycles

theorem toAtomicCycles_ofAtomicCycles {next : V -> V}
    (selected : Finset (finiteCRSFAtomicCycle next)) :
    (ofAtomicCycles selected).toAtomicCycles = selected := by
  ext cycle
  rw [mem_toAtomicCycles_iff_support_subset]
  constructor
  · intro hsubset
    obtain ⟨v, hv⟩ := cycle.2.1.nonempty_support
    have hvUnion := hsubset hv
    change v ∈ selected.biUnion (fun cycle => cycle.1.support) at hvUnion
    rw [Finset.mem_biUnion] at hvUnion
    rcases hvUnion with ⟨cycle', hcycle', hv'⟩
    have hcycles : cycle = cycle' := by
      by_contra hne
      exact (Finset.disjoint_left.mp
        (finiteCRSFAtomicCycle_support_disjoint hne) hv) hv'
    simpa [hcycles] using hcycle'
  · intro hcycle v hv
    change v ∈ selected.biUnion (fun cycle => cycle.1.support)
    rw [Finset.mem_biUnion]
    exact ⟨cycle, hcycle, hv⟩



noncomputable def equivAtomicCycles (next : V -> V) :
    finiteCRSFCycleSupport next ≃ Finset (finiteCRSFAtomicCycle next) where
  toFun := toAtomicCycles
  invFun := ofAtomicCycles
  left_inv := ofAtomicCycles_toAtomicCycles
  right_inv := toAtomicCycles_ofAtomicCycles


noncomputable def atomicCycleHolonomy {next : V -> V}
    (transport : V -> V -> Complex) (S : finiteCRSFCycleSupport next)
    (cycle : Equiv.Perm (↑S.carrier)) : Complex :=
  ∏ v ∈ cycle.support, transport v (next v)

theorem support_toAtomicCycle {next : V -> V}
    (S : finiteCRSFCycleSupport next)
    (cycle : {cycle // cycle ∈ S.atomicCycles}) :
    (S.toAtomicCycle cycle).1.support =
      cycle.1.support.map (Function.Embedding.subtype fun v => v ∈ S.carrier) := by
  change (Equiv.Perm.ofSubtype cycle.1).support = _
  ext v
  constructor
  · intro hv
    have hvcarrier : v ∈ S.carrier := by
      by_contra hcarrier
      exact (Equiv.Perm.mem_support.mp hv)
        (Equiv.Perm.ofSubtype_apply_of_not_mem _ hcarrier)
    rw [Finset.mem_map]
    refine ⟨⟨v, hvcarrier⟩, ?_, rfl⟩
    rw [Equiv.Perm.mem_support]
    intro hfixed
    apply Equiv.Perm.mem_support.mp hv
    rw [Equiv.Perm.ofSubtype_apply_of_mem _ hvcarrier]
    exact congrArg Subtype.val hfixed
  · intro hv
    rw [Finset.mem_map] at hv
    rcases hv with ⟨w, hw, rfl⟩
    rw [Equiv.Perm.mem_support]
    change (Equiv.Perm.ofSubtype cycle.1) (w : V) ≠ (w : V)
    rw [Equiv.Perm.ofSubtype_apply_of_mem _ w.property]
    intro hfixed
    exact (Equiv.Perm.mem_support.mp hw) (Subtype.ext hfixed)

theorem holonomy_toAtomicCycle {next : V -> V}
    (transport : V -> V -> Complex) (S : finiteCRSFCycleSupport next)
    (cycle : {cycle // cycle ∈ S.atomicCycles}) :
    (S.toAtomicCycle cycle).holonomy transport =
      S.atomicCycleHolonomy transport cycle.1 := by
  unfold finiteCRSFAtomicCycle.holonomy atomicCycleHolonomy
  change (∏ v ∈ (Equiv.Perm.ofSubtype cycle.1).support,
      transport v (next v)) = _
  have hsupp : (Equiv.Perm.ofSubtype cycle.1).support =
      cycle.1.support.map
        (Function.Embedding.subtype fun v => v ∈ S.carrier) :=
    S.support_toAtomicCycle cycle
  rw [hsupp, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro v _
  rfl

theorem card_toAtomicCycles {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    S.toAtomicCycles.card = S.atomicCycles.card := by
  simp [toAtomicCycles]

theorem prod_holonomy_toAtomicCycles {next : V -> V}
    (transport : V -> V -> Complex) (S : finiteCRSFCycleSupport next) :
    (∏ cycle ∈ S.toAtomicCycles, cycle.holonomy transport) =
      ∏ cycle ∈ S.atomicCycles,
        S.atomicCycleHolonomy transport cycle := by
  rw [toAtomicCycles, Finset.prod_map]
  calc
    (∏ cycle : {cycle // cycle ∈ S.atomicCycles},
        (S.toAtomicCycle cycle).holonomy transport) =
      ∏ cycle : {cycle // cycle ∈ S.atomicCycles},
        S.atomicCycleHolonomy transport cycle.1 := by
      apply Finset.prod_congr rfl
      intro cycle _
      exact S.holonomy_toAtomicCycle transport cycle
    _ = ∏ cycle ∈ S.atomicCycles,
        S.atomicCycleHolonomy transport cycle := by
      symm
      apply Finset.prod_subtype
      simp



theorem prod_transport_eq_prod_atomicCycleHolonomy {next : V -> V}
    (transport : V -> V -> Complex) (S : finiteCRSFCycleSupport next) :
    (∏ v ∈ S.carrier, transport v (next v)) =
      ∏ cycle ∈ S.atomicCycles,
        S.atomicCycleHolonomy transport cycle := by
  have hunion :
      (Finset.univ : Finset (↑S.carrier)) =
        S.atomicCycles.biUnion fun cycle => cycle.support := by
    ext v
    simp only [Finset.mem_univ, true_iff, Finset.mem_biUnion]
    exact S.exists_mem_atomicCycle v
  have hpairwise :
      Set.PairwiseDisjoint
        (↑S.atomicCycles : Set (Equiv.Perm (↑S.carrier)))
        (fun cycle : Equiv.Perm (↑S.carrier) => cycle.support) := by
    intro cycle hcycle cycle' hcycle' hne
    apply Equiv.Perm.Disjoint.disjoint_support
    exact Equiv.Perm.cycleFactorsFinset_pairwise_disjoint
      S.restrictedPerm hcycle hcycle' hne
  calc
    (∏ v ∈ S.carrier, transport v (next v)) =
        ∏ v : ↑S.carrier, transport v (next v) := by
      apply Finset.prod_subtype
      simp
    _ = ∏ v ∈ (Finset.univ : Finset (↑S.carrier)),
          transport v (next v) := by simp
    _ = ∏ v ∈ (S.atomicCycles.biUnion fun cycle => cycle.support),
          transport v (next v) := by rw [← hunion]
    _ = ∏ cycle ∈ S.atomicCycles,
          ∏ v ∈ cycle.support, transport v (next v) :=
      Finset.prod_biUnion hpairwise
    _ = ∏ cycle ∈ S.atomicCycles,
          S.atomicCycleHolonomy transport cycle := by
      rfl



theorem sign_ambientPerm_eq_atomicCycles {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    Equiv.Perm.sign S.ambientPerm =
      (-1 : ℤˣ) ^ (S.carrier.card + S.atomicCycles.card) := by
  calc
    Equiv.Perm.sign S.ambientPerm =
        Equiv.Perm.sign S.restrictedPerm.symm := by
      exact Equiv.Perm.sign_ofSubtype S.restrictedPerm.symm
    _ = Equiv.Perm.sign S.restrictedPerm := by
      rw [Equiv.Perm.sign_symm]
    _ = (-1 : ℤˣ) ^ (S.carrier.card + S.atomicCycles.card) := by
      rw [Equiv.Perm.sign_of_cycleType, Equiv.Perm.sum_cycleType,
        S.restrictedPerm_support]
      simp [atomicCycles, Equiv.Perm.cycleType_def]
      rfl

end finiteCRSFCycleSupport



noncomputable def finiteCRSFWitnessFiber.toCycleSupport
    {next : V -> V} (X : finiteCRSFWitnessFiber next) :
    finiteCRSFCycleSupport next where
  carrier := X.1.1.support
  mapsTo := by
    intro v hv
    have hxv : next v = finiteCRSFWitnessNext X.1 v :=
      (congrFun X.2 v).symm
    rw [hxv]
    have hv' : X.1.1 v ≠ v := Equiv.Perm.mem_support.mp hv
    have hnext : finiteCRSFWitnessNext X.1 v = X.1.1.symm v := by
      simp [finiteCRSFWitnessNext, hv']
    rw [hnext, Equiv.Perm.mem_support]
    intro hfixed
    have hbad : X.1.1 v = v := by
      simpa only [X.1.1.apply_symm_apply] using congrArg X.1.1 hfixed
    exact hv' hbad
  injOn := by
    intro a ha b hb hab
    apply finiteCRSFWitnessNext_injectiveOn_support X.1 ha hb
    calc
      finiteCRSFWitnessNext X.1 a = next a := congrFun X.2 a
      _ = next b := hab
      _ = finiteCRSFWitnessNext X.1 b := (congrFun X.2 b).symm
  noFixed := by
    intro v hv
    have hv' : X.1.1 v ≠ v := Equiv.Perm.mem_support.mp hv
    intro hnext
    have hfixed : finiteCRSFWitnessNext X.1 v = v := by
      rw [X.2]
      exact hnext
    have hfixed' : X.1.1.symm v = v := by
      simpa only [finiteCRSFWitnessNext, dif_neg hv'] using hfixed
    have hbad : v = X.1.1 v := by
      simpa only [X.1.1.apply_symm_apply] using congrArg X.1.1 hfixed'
    exact hv' hbad.symm

theorem finiteCRSFCycleSupport.toFiber_support {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    S.toFiber.1.1.support = S.carrier := by
  exact S.ambientPerm_support

theorem finiteCRSFCycleSupport.toCycleSupport_toFiber {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    S.toFiber.toCycleSupport = S := by
  apply finiteCRSFCycleSupport.ext
  exact S.toFiber_support



theorem finiteCRSFWitnessFiber_support_injective (next : V -> V) :
    Function.Injective
      (fun X : finiteCRSFWitnessFiber next => X.1.1.support) := by
  intro X Y hsupp
  rcases X with ⟨⟨sigma, target⟩, hX⟩
  rcases Y with ⟨⟨tau, target'⟩, hY⟩
  change sigma.support = tau.support at hsupp
  have hperm : sigma = tau := by
    apply Equiv.ext
    intro v
    by_cases hv : sigma v = v
    · have hnot : v ∉ sigma.support := by
        simp [Equiv.Perm.mem_support, hv]
      have hnot' : v ∉ tau.support := by
        rw [← hsupp]
        exact hnot
      have htau : tau v = v := by
        simpa [Equiv.Perm.mem_support] using hnot'
      exact hv.trans htau.symm
    · have hvtau : tau v ≠ v := by
        have hmem : v ∈ sigma.support := Equiv.Perm.mem_support.mpr hv
        rw [hsupp] at hmem
        exact Equiv.Perm.mem_support.mp hmem
      have hsigmaImage : sigma v ∈ sigma.support := by
        rw [Equiv.Perm.mem_support]
        intro h
        exact hv (sigma.injective h)
      have htauImage : tau v ∈ sigma.support := by
        rw [hsupp, Equiv.Perm.mem_support]
        intro h
        exact hvtau (tau.injective h)
      apply (finiteCRSFWitnessNext_injectiveOn_support
        (⟨sigma, target⟩ : finiteCRSFWitness V)) hsigmaImage htauImage
      calc
        finiteCRSFWitnessNext
            (⟨sigma, target⟩ : finiteCRSFWitness V) (sigma v) = v :=
          finiteCRSFWitnessNext_nonfixed_cycle
            (⟨sigma, target⟩ : finiteCRSFWitness V) v hv
        _ = finiteCRSFWitnessNext
            (⟨tau, target'⟩ : finiteCRSFWitness V) (tau v) :=
          (finiteCRSFWitnessNext_nonfixed_cycle
            (⟨tau, target'⟩ : finiteCRSFWitness V) v hvtau).symm
        _ = finiteCRSFWitnessNext
            (⟨sigma, target⟩ : finiteCRSFWitness V) (tau v) := by
          rw [hX, hY]
  subst tau
  have htarget : target = target' := by
    funext v
    calc
      target v = finiteCRSFWitnessNext
          (⟨sigma, target⟩ : finiteCRSFWitness V) v := by
        symm
        simpa using finiteCRSFWitnessNext_fixed
          (⟨sigma, target⟩ : finiteCRSFWitness V) (v : V) v.property
      _ = next v := congrFun hX v
      _ = finiteCRSFWitnessNext
          (⟨sigma, target'⟩ : finiteCRSFWitness V) v :=
        (congrFun hY v).symm
      _ = target' v := by
        simpa using finiteCRSFWitnessNext_fixed
          (⟨sigma, target'⟩ : finiteCRSFWitness V) (v : V) v.property
  subst target'
  rfl

theorem finiteCRSFWitnessFiber.toFiber_toCycleSupport {next : V -> V}
    (X : finiteCRSFWitnessFiber next) :
    X.toCycleSupport.toFiber = X := by
  apply finiteCRSFWitnessFiber_support_injective next
  exact X.toCycleSupport.toFiber_support



noncomputable def finiteCRSFWitnessFiberEquivCRSFCycleSupport
    (next : V -> V) :
    finiteCRSFWitnessFiber next ≃ finiteCRSFCycleSupport next where
  toFun := finiteCRSFWitnessFiber.toCycleSupport
  invFun := finiteCRSFCycleSupport.toFiber
  left_inv := finiteCRSFWitnessFiber.toFiber_toCycleSupport
  right_inv := finiteCRSFCycleSupport.toCycleSupport_toFiber

noncomputable instance finiteCRSFCycleSupportFintype (next : V -> V) :
    Fintype (finiteCRSFCycleSupport next) :=
  Fintype.ofEquiv (finiteCRSFWitnessFiber next)
    (finiteCRSFWitnessFiberEquivCRSFCycleSupport next)



theorem finiteCRSFWitnessTerm_toFiber
    (conductance transport : V -> V -> Complex) (next : V -> V)
    (S : finiteCRSFCycleSupport next) :
    finiteCRSFWitnessTerm conductance transport S.toFiber =
      S.term conductance transport := by
  have hfixed :
      (∏ v : laplacianPermutationFixedPoint S.ambientPerm,
          conductance v (next v)) =
        ∏ v ∈ (Finset.univ.filter fun v => v ∉ S.carrier),
          conductance v (next v) := by
    symm
    apply Finset.prod_subtype
    intro v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact S.ambientPerm_apply_of_not_mem
    · intro hfixed hv
      exact S.ambientPerm_ne_of_mem hv hfixed
  have hnonfixedSet :
      (Finset.univ.filter fun v => S.ambientPerm v ≠ v) = S.carrier := by
    ext v
    rw [← S.ambientPerm_support]
    simp [Equiv.Perm.mem_support]
  have hcarrierPermuted (v : V) :
      v ∈ S.carrier ↔ S.ambientPerm v ∈ S.carrier := by
    rw [← S.ambientPerm_support]
    exact Equiv.Perm.apply_mem_support.symm
  have hnonfixed :
      (∏ v ∈ (Finset.univ.filter fun v => S.ambientPerm v ≠ v),
          -conductance (S.ambientPerm v) v *
            transport (S.ambientPerm v) v) =
        ∏ v ∈ S.carrier,
          -conductance v (next v) * transport v (next v) := by
    rw [hnonfixedSet]
    apply Finset.prod_equiv S.ambientPerm
    · exact hcarrierPermuted
    · intro v hv
      have himage : S.ambientPerm v ∈ S.carrier :=
        (hcarrierPermuted v).mp hv
      have hnext : next (S.ambientPerm v) = v := by
        rw [← S.ambientPerm_symm_apply_of_mem himage]
        exact S.ambientPerm.symm_apply_apply v
      rw [hnext]
  change Equiv.Perm.sign S.ambientPerm •
      ((∏ v : laplacianPermutationFixedPoint S.ambientPerm,
          conductance v (next v)) *
        ∏ v ∈ (Finset.univ.filter fun v => S.ambientPerm v ≠ v),
          -conductance (S.ambientPerm v) v *
            transport (S.ambientPerm v) v) =
    Equiv.Perm.sign S.ambientPerm •
      ((∏ v ∈ (Finset.univ.filter fun v => v ∉ S.carrier),
          conductance v (next v)) *
        ∏ v ∈ S.carrier,
          -conductance v (next v) * transport v (next v))
  rw [hfixed, hnonfixed]



theorem finiteCRSFCycleSupport.term_eq_atomicCycleSign
    (conductance transport : V -> V -> Complex) (next : V -> V)
    (S : finiteCRSFCycleSupport next) :
    S.term conductance transport =
      (-1 : Complex) ^ S.atomicCycles.card *
        ((∏ v ∈ (Finset.univ.filter fun v => v ∉ S.carrier),
            conductance v (next v)) *
          ∏ v ∈ S.carrier,
            conductance v (next v) * transport v (next v)) := by
  unfold finiteCRSFCycleSupport.term
  rw [S.sign_ambientPerm_eq_atomicCycles]
  simp_rw [neg_mul]
  rw [Finset.prod_neg]
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul Complex, smul_eq_mul]
  have hcast (n : Nat) :
      ((↑(↑((-1 : ℤˣ) ^ n) : ℤ) : Complex)) =
        (-1 : Complex) ^ n := by
    change (((((-1 : ℤˣ) : ℤ) ^ n : ℤ) : Complex)) = _
    rw [Int.cast_pow]
    norm_num
  rw [hcast, pow_add]
  have hcancel :
      (-1 : Complex) ^ S.carrier.card *
          (-1 : Complex) ^ S.carrier.card = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    ((-1 : Complex) ^ S.carrier.card *
          (-1 : Complex) ^ S.atomicCycles.card) *
        ((∏ v ∈ (Finset.univ.filter fun v => v ∉ S.carrier),
            conductance v (next v)) *
          ((-1 : Complex) ^ S.carrier.card *
            ∏ v ∈ S.carrier,
              conductance v (next v) * transport v (next v))) =
      ((-1 : Complex) ^ S.carrier.card *
          (-1 : Complex) ^ S.carrier.card) *
        ((-1 : Complex) ^ S.atomicCycles.card *
          ((∏ v ∈ (Finset.univ.filter fun v => v ∉ S.carrier),
              conductance v (next v)) *
            ∏ v ∈ S.carrier,
              conductance v (next v) * transport v (next v))) := by
        ring
    _ = _ := by rw [hcancel, one_mul]



theorem finiteCRSFCycleSupport.term_eq_atomicCycleHolonomies
    (conductance transport : V -> V -> Complex) (next : V -> V)
    (S : finiteCRSFCycleSupport next) :
    S.term conductance transport =
      (-1 : Complex) ^ S.atomicCycles.card *
        ((∏ v : V, conductance v (next v)) *
          ∏ cycle ∈ S.atomicCycles,
            S.atomicCycleHolonomy transport cycle) := by
  rw [S.term_eq_atomicCycleSign]
  have hinside :
      (∏ v ∈ S.carrier,
          conductance v (next v) * transport v (next v)) =
        (∏ v ∈ S.carrier, conductance v (next v)) *
          ∏ v ∈ S.carrier, transport v (next v) := by
    exact Finset.prod_mul_distrib
  rw [hinside]
  rw [prod_transport_eq_prod_atomicCycleHolonomy transport S]
  have hpartition :
      (∏ v ∈ (Finset.univ.filter fun v => v ∉ S.carrier),
          conductance v (next v)) *
        (∏ v ∈ S.carrier, conductance v (next v)) =
      ∏ v : V, conductance v (next v) := by
    have hcarrierFilter :
        (Finset.univ.filter fun v : V => v ∈ S.carrier) = S.carrier := by
      ext v
      simp
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_not,
      hcarrierFilter] using
      (Finset.prod_filter_mul_prod_filter_not
        (Finset.univ : Finset V) (fun v => v ∉ S.carrier)
        (fun v => conductance v (next v)))
  calc
    (-1 : Complex) ^ S.atomicCycles.card *
        ((∏ v ∈ (Finset.univ.filter fun v => v ∉ S.carrier),
            conductance v (next v)) *
          ((∏ v ∈ S.carrier, conductance v (next v)) *
            ∏ cycle ∈ S.atomicCycles,
              S.atomicCycleHolonomy transport cycle)) =
      (-1 : Complex) ^ S.atomicCycles.card *
        (((∏ v ∈ (Finset.univ.filter fun v => v ∉ S.carrier),
            conductance v (next v)) *
          (∏ v ∈ S.carrier, conductance v (next v))) *
            ∏ cycle ∈ S.atomicCycles,
              S.atomicCycleHolonomy transport cycle) := by ring
    _ = _ := by rw [hpartition]



def finiteCRSFCycleSupportSelection (next : V -> V) : Type _ :=
  Set.range
    (fun X : finiteCRSFWitnessFiber next => X.1.1.support)


noncomputable def finiteCRSFWitnessFiberEquivCycleSupport
    (next : V -> V) :
    finiteCRSFWitnessFiber next ≃ finiteCRSFCycleSupportSelection next :=
  Equiv.ofInjective
    (fun X : finiteCRSFWitnessFiber next => X.1.1.support)
    (finiteCRSFWitnessFiber_support_injective next)


theorem det_finiteTwistedLaplacian_eq_sum_finiteCRSFWitnessFiber
    (conductance transport : V -> V -> Complex) :
    (finiteTwistedLaplacian conductance transport).det =
      ∑ next : V -> V,
        ∑ X : finiteCRSFWitnessFiber next,
          finiteCRSFWitnessTerm conductance transport X := by
  rw [det_finiteTwistedLaplacian_eq_sum_finiteCRSFWitness]
  symm
  exact Fintype.sum_fiberwise finiteCRSFWitnessNext
    (finiteCRSFWitnessTerm conductance transport)



theorem det_finiteTwistedLaplacian_eq_sum_finiteCRSFCycleSupport
    (conductance transport : V -> V -> Complex) :
    (finiteTwistedLaplacian conductance transport).det =
      ∑ next : V -> V,
        ∑ S : finiteCRSFCycleSupport next,
          finiteCRSFWitnessTerm conductance transport S.toFiber := by
  rw [det_finiteTwistedLaplacian_eq_sum_finiteCRSFWitnessFiber]
  apply Finset.sum_congr rfl
  intro next _
  exact Fintype.sum_equiv
    (finiteCRSFWitnessFiberEquivCRSFCycleSupport next)
    (fun X : finiteCRSFWitnessFiber next =>
      finiteCRSFWitnessTerm conductance transport X)
    (fun S : finiteCRSFCycleSupport next =>
      finiteCRSFWitnessTerm conductance transport S.toFiber)
    (fun X => by
      change finiteCRSFWitnessTerm conductance transport X.1 =
        finiteCRSFWitnessTerm conductance transport
          X.toCycleSupport.toFiber.1
      exact congrArg (finiteCRSFWitnessTerm conductance transport)
        (congrArg Subtype.val X.toFiber_toCycleSupport.symm))



theorem det_finiteTwistedLaplacian_eq_sum_finiteCRSFCycleSupportTerm
    (conductance transport : V -> V -> Complex) :
    (finiteTwistedLaplacian conductance transport).det =
      ∑ next : V -> V,
        ∑ S : finiteCRSFCycleSupport next,
          S.term conductance transport := by
  rw [det_finiteTwistedLaplacian_eq_sum_finiteCRSFCycleSupport]
  apply Finset.sum_congr rfl
  intro next _
  apply Finset.sum_congr rfl
  intro S _
  exact finiteCRSFWitnessTerm_toFiber conductance transport next S




theorem det_finiteTwistedLaplacian_eq_sum_atomicCycleHolonomies
    (conductance transport : V -> V -> Complex) :
    (finiteTwistedLaplacian conductance transport).det =
      ∑ next : V -> V,
        (∏ v : V, conductance v (next v)) *
          ∑ S : finiteCRSFCycleSupport next,
            (-1 : Complex) ^ S.atomicCycles.card *
              ∏ cycle ∈ S.atomicCycles,
                S.atomicCycleHolonomy transport cycle := by
  rw [det_finiteTwistedLaplacian_eq_sum_finiteCRSFCycleSupportTerm]
  apply Finset.sum_congr rfl
  intro next _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [S.term_eq_atomicCycleHolonomies]
  ring



theorem finiteTwistedLaplacian_trivial_mulVec_one
    (conductance : V -> V -> Complex)
    (hdiag : forall v, conductance v v = 0) :
    finiteTwistedLaplacian conductance (fun _ _ => 1) *ᵥ
        (fun _ => (1 : Complex)) = 0 := by
  funext v
  rw [Matrix.mulVec, dotProduct]
  simp only [mul_one, Pi.zero_apply]
  rw [← Finset.sum_erase_add Finset.univ
    (fun w => finiteTwistedLaplacian conductance (fun _ _ => 1) v w)
    (Finset.mem_univ v)]
  simp only [finiteTwistedLaplacian, if_pos]
  have hoff :
      (∑ x ∈ Finset.univ.erase v,
        if v = x then ∑ u, conductance v u else -conductance v x * 1) =
        ∑ x ∈ Finset.univ.erase v, -conductance v x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxne : x ≠ v := Finset.ne_of_mem_erase hx
    simp [hxne.symm]
  rw [hoff, ← Finset.sum_erase_add Finset.univ
    (fun w => conductance v w) (Finset.mem_univ v)]
  rw [hdiag]
  simp



theorem det_finiteTwistedLaplacian_trivial_eq_zero
    [Nonempty V] (conductance : V -> V -> Complex)
    (hdiag : forall v, conductance v v = 0) :
    (finiteTwistedLaplacian conductance (fun _ _ => 1)).det = 0 := by
  let v0 : V := Classical.choice (inferInstance : Nonempty V)
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
    (finiteTwistedLaplacian_trivial_mulVec_one conductance hdiag)
    (i := v0)
  simp


theorem finiteTwistedLaplacian_const_mul
    (a : Complex) (conductance transport : V -> V -> Complex) :
    finiteTwistedLaplacian (fun v w => a * conductance v w) transport =
      a • finiteTwistedLaplacian conductance transport := by
  ext v w
  by_cases hvw : v = w
  · subst w
    simp [finiteTwistedLaplacian, Finset.mul_sum]
  · simp [finiteTwistedLaplacian, hvw]
    ring



theorem det_finiteTwistedLaplacian_const_mul
    (a : Complex) (conductance transport : V -> V -> Complex) :
    (finiteTwistedLaplacian (fun v w => a * conductance v w)
        transport).det =
      a ^ Fintype.card V *
        (finiteTwistedLaplacian conductance transport).det := by
  rw [finiteTwistedLaplacian_const_mul, Matrix.det_smul]


noncomputable def isoradialLaplacianConductance
    (theta : V -> V -> Real) : V -> V -> Complex :=
  fun v w => (Real.tan (theta v w) : Complex)



noncomputable def isoradialMuConductance
    (theta : V -> V -> Real) : V -> V -> Complex :=
  fun v w => isoradialCriticalMu (theta v w)

omit [Fintype V] [DecidableEq V] in
theorem isoradialMuConductance_eq_I_mul
    (theta : V -> V -> Real) :
    isoradialMuConductance theta =
      fun v w => Complex.I * isoradialLaplacianConductance theta v w := by
  funext v w
  rfl


theorem finiteTwistedLaplacian_isoradialMu
    (theta : V -> V -> Real) (transport : V -> V -> Complex) :
    finiteTwistedLaplacian (isoradialMuConductance theta) transport =
      Complex.I • finiteTwistedLaplacian
        (isoradialLaplacianConductance theta) transport := by
  rw [isoradialMuConductance_eq_I_mul,
    finiteTwistedLaplacian_const_mul]


theorem det_finiteTwistedLaplacian_isoradialMu
    (theta : V -> V -> Real) (transport : V -> V -> Complex) :
    (finiteTwistedLaplacian (isoradialMuConductance theta) transport).det =
      Complex.I ^ Fintype.card V *
        (finiteTwistedLaplacian
          (isoradialLaplacianConductance theta) transport).det := by
  rw [finiteTwistedLaplacian_isoradialMu, Matrix.det_smul]



def coneQuarterPhase (exceptional : V -> Bool) (v : V) : Complex :=
  if exceptional v then -Complex.I else Complex.I


def coneExceptionCount (exceptional : V -> Bool) : Nat :=
  (Finset.univ.filter fun v => exceptional v = true).card

omit [Fintype V] [DecidableEq V] in
theorem neg_one_mul_coneQuarterPhase_mul_I
    (exceptional : V -> Bool) (v : V) :
    (-1 : Complex) * coneQuarterPhase exceptional v * Complex.I =
      if exceptional v then -1 else 1 := by
  cases h : exceptional v <;>
    simp [coneQuarterPhase, h, Complex.I_mul_I]

omit [DecidableEq V] in


theorem conePhase_prefactor_eq_exceptionSign
    (exceptional : V -> Bool) :
    (-1 : Complex) ^ Fintype.card V *
        (∏ v : V, coneQuarterPhase exceptional v) *
        Complex.I ^ Fintype.card V =
      (-1 : Complex) ^ coneExceptionCount exceptional := by
  have hneg : (∏ _v : V, (-1 : Complex)) =
      (-1 : Complex) ^ Fintype.card V := by simp
  have hI : (∏ _v : V, Complex.I) =
      Complex.I ^ Fintype.card V := by simp
  rw [← hneg, ← hI,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  calc
    (∏ v : V, (-1 : Complex) * coneQuarterPhase exceptional v * Complex.I) =
        ∏ v : V, if exceptional v then (-1 : Complex) else 1 := by
      apply Finset.prod_congr rfl
      intro v _
      exact neg_one_mul_coneQuarterPhase_mul_I exceptional v
    _ = (-1 : Complex) ^ coneExceptionCount exceptional := by
      rw [coneExceptionCount, Finset.prod_ite]
      simp



noncomputable def kwEulerPowerPrefactor (vertexCount edgeCount : Nat) : Complex :=
  (2 : Complex) ^ edgeCount / (2 : Complex) ^ vertexCount


noncomputable def kwLaplacianEdgePrefactor (theta : E -> Real) : Complex :=
  ∏ e : E,
    (Real.cos (theta e) : Complex) / (1 + Real.cos (theta e) : Real)


noncomputable def formanCycleCoefficient (holonomy : Complex) : Complex :=
  2 - holonomy - holonomy⁻¹



noncomputable def formanCRSFCoefficient
    {C : Type*} [Fintype C] (holonomy : C -> Complex) : Complex :=
  ∏ component : C, formanCycleCoefficient (holonomy component)




theorem sum_cycleSelections_eq_prod_one_sub
    {C : Type*} [Fintype C]
    (holonomy : C -> Complex) :
    (∑ selected : Finset C,
        (-1 : Complex) ^ selected.card *
          ∏ c ∈ selected, holonomy c) =
      ∏ c : C, (1 - holonomy c) := by
  classical
  have h := Fintype.prod_add
    (fun c : C => -holonomy c) (fun _c : C => (1 : Complex))
  symm
  simpa [prod_neg, sub_eq_add_neg, add_comm, mul_comm] using h



theorem pairedBoundaryCharacter_eq_formanCycleCoefficient
    (holonomy : Complex) (hholonomy : holonomy ≠ 0) :
    (1 - holonomy) * (1 - holonomy⁻¹) =
      formanCycleCoefficient holonomy := by
  unfold formanCycleCoefficient
  rw [mul_sub, mul_one]
  have hinv : holonomy * holonomy⁻¹ = 1 :=
    mul_inv_cancel₀ hholonomy
  rw [sub_mul, one_mul, hinv]
  ring



theorem prod_pairedBoundaryCharacter_eq_formanCRSFCoefficient
    {C : Type*} [Fintype C]
    (holonomy : C -> Complex) (hholonomy : forall c, holonomy c ≠ 0) :
    (∏ c : C, (1 - holonomy c) * (1 - (holonomy c)⁻¹)) =
      formanCRSFCoefficient holonomy := by
  unfold formanCRSFCoefficient
  apply Finset.prod_congr rfl
  intro c _
  exact pairedBoundaryCharacter_eq_formanCycleCoefficient
    (holonomy c) (hholonomy c)

omit [DecidableEq E] in







theorem criticalKacWard_det_eq_laplacian_of_subgraphFactorization
    (kacWard : Matrix D D Complex)
    (thetaVertex : V -> V -> Real) (thetaEdge : E -> Real)
    (transport : V -> V -> Complex) (exceptional : V -> Bool)
    (hsubgraphFactorization :
      (1 - kacWard).det =
        (((-1 : Complex) ^ Fintype.card V *
            kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
            (∏ v : V, coneQuarterPhase exceptional v) *
            kwLaplacianEdgePrefactor thetaEdge) *
          (finiteTwistedLaplacian
            (isoradialMuConductance thetaVertex) transport).det)) :
    (1 - kacWard).det =
      (-1 : Complex) ^ coneExceptionCount exceptional *
        kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
        kwLaplacianEdgePrefactor thetaEdge *
        (finiteTwistedLaplacian
          (isoradialLaplacianConductance thetaVertex) transport).det := by
  rw [hsubgraphFactorization,
    det_finiteTwistedLaplacian_isoradialMu]
  calc
    ((-1 : Complex) ^ Fintype.card V *
          kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
          (∏ v : V, coneQuarterPhase exceptional v) *
          kwLaplacianEdgePrefactor thetaEdge) *
        (Complex.I ^ Fintype.card V *
          (finiteTwistedLaplacian
            (isoradialLaplacianConductance thetaVertex) transport).det) =
      (((-1 : Complex) ^ Fintype.card V *
          (∏ v : V, coneQuarterPhase exceptional v) *
          Complex.I ^ Fintype.card V) *
        kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
        kwLaplacianEdgePrefactor thetaEdge *
        (finiteTwistedLaplacian
          (isoradialLaplacianConductance thetaVertex) transport).det) := by
      ring
    _ = (-1 : Complex) ^ coneExceptionCount exceptional *
        kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
        kwLaplacianEdgePrefactor thetaEdge *
        (finiteTwistedLaplacian
          (isoradialLaplacianConductance thetaVertex) transport).det := by
      rw [conePhase_prefactor_eq_exceptionSign]

end StatMech.FrontierA
