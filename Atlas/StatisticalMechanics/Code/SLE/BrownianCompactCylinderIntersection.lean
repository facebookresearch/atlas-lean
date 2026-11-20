/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.SLE.BrownianProjectiveContent
import Mathlib.Topology.Bornology.Constructions
import Mathlib.Topology.MetricSpace.Bounded









open MeasureTheory Set

namespace StatMech.SLE



theorem nonempty_iInter_cylinder_of_compact
    (I : Nat -> Finset Real)
    (S : forall n, Set (I n -> Real))
    (hcompact : forall n, IsCompact (S n))
    (hnonempty : forall n, (S n).Nonempty)
    (hanti : Antitone (fun n =>
      (cylinder (I n) (S n) : Set (Real -> Real)))) :
    (iInter (fun n =>
      (cylinder (I n) (S n) : Set (Real -> Real)))).Nonempty := by
  classical
  let C : Nat -> Set (Real -> Real) := fun n => cylinder (I n) (S n)
  let K : Real -> Set Real := fun t =>
    if ht : exists n, t ∈ I n then
      (fun x : I (Nat.find ht) -> Real =>
        x ⟨t, Nat.find_spec ht⟩) '' S (Nat.find ht)
    else
      {0}
  have hKcompact (t : Real) : IsCompact (K t) := by
    by_cases ht : exists n, t ∈ I n
    · dsimp only [K]
      rw [dif_pos ht]
      exact (hcompact (Nat.find ht)).image (continuous_apply _)
    · dsimp only [K]
      rw [dif_neg ht]
      exact isCompact_singleton
  have hKnonempty (t : Real) : (K t).Nonempty := by
    by_cases ht : exists n, t ∈ I n
    · dsimp only [K]
      rw [dif_pos ht]
      obtain ⟨x, hx⟩ := hnonempty (Nat.find ht)
      exact ⟨x ⟨t, Nat.find_spec ht⟩, x, hx, rfl⟩
    · dsimp only [K]
      rw [dif_neg ht]
      exact singleton_nonempty 0
  let P : Set (Real -> Real) := Set.pi Set.univ K
  have hPcompact : IsCompact P := by
    simpa only [P] using isCompact_univ_pi hKcompact
  have hCclosed (n : Nat) : IsClosed (C n) := by
    simpa only [C] using (hcompact n).isClosed.cylinder (I n)
  have hCnonemptyInP (n : Nat) : (P ∩ C n).Nonempty := by
    obtain ⟨y, hy⟩ := hnonempty n
    let pick : Real -> Real := fun t => (hKnonempty t).some
    let f : Real -> Real := fun t =>
      if ht : t ∈ I n then y ⟨t, ht⟩ else pick t
    have hfC : f ∈ C n := by
      change (fun i : I n => f i) ∈ S n
      simpa only [f, Finset.coe_mem, dite_true] using hy
    have hfP : f ∈ P := by
      change f ∈ Set.pi Set.univ K
      rw [Set.mem_pi]
      intro t _htuniv
      by_cases ht : t ∈ I n
      · let htUsed : exists k, t ∈ I k := ⟨n, ht⟩
        have hfirstLe : Nat.find htUsed ≤ n := Nat.find_min' htUsed ht
        have hfirstCylinder : f ∈ C (Nat.find htUsed) :=
          hanti hfirstLe hfC
        dsimp only [K]
        rw [dif_pos htUsed]
        refine ⟨fun i : I (Nat.find htUsed) => f i, ?_, ?_⟩
        · exact hfirstCylinder
        · simp only [f, ht, dite_true]
      · simpa only [f, ht, dite_false, pick] using
          (hKnonempty t).choose_spec
    exact ⟨f, hfP, hfC⟩
  let D : Nat -> Set (Real -> Real) := fun n => P ∩ C n
  have hDsucc (n : Nat) : D (n + 1) ⊆ D n := by
    intro f hf
    exact ⟨hf.1, hanti (Nat.le_succ n) hf.2⟩
  have hDnonempty (n : Nat) : (D n).Nonempty := hCnonemptyInP n
  have hDzeroCompact : IsCompact (D 0) :=
    hPcompact.inter_right (hCclosed 0)
  have hDclosed (n : Nat) : IsClosed (D n) :=
    hPcompact.isClosed.inter (hCclosed n)
  obtain ⟨f, hf⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      D hDsucc hDnonempty hDzeroCompact hDclosed
  refine ⟨f, Set.mem_iInter.2 fun n => ?_⟩
  exact (Set.mem_iInter.1 hf n).2


noncomputable def cylinderPrefixSupport
    (I : Nat -> Finset Real) (n : Nat) : Finset Real :=
  (Finset.range (n + 1)).biUnion I

theorem cylinderPrefixSupport_subset
    (I : Nat -> Finset Real) {k n : Nat} (hkn : k <= n) :
    I k <= cylinderPrefixSupport I n := by
  intro t ht
  rw [cylinderPrefixSupport, Finset.mem_biUnion]
  exact ⟨k, Finset.mem_range.2 (by omega), ht⟩



noncomputable def cylinderPrefixBase
    (I : Nat -> Finset Real) (L : forall k, Set (I k -> Real))
    (n : Nat) : Set (cylinderPrefixSupport I n -> Real) :=
  {x | forall (k : Nat) (hkn : k <= n),
    Finset.restrict₂
      (π := fun _ : Real => Real)
      (cylinderPrefixSupport_subset I hkn) x ∈ L k}



theorem cylinder_cylinderPrefixBase
    (I : Nat -> Finset Real) (L : forall k, Set (I k -> Real))
    (n : Nat) :
    (cylinder (cylinderPrefixSupport I n) (cylinderPrefixBase I L n) :
        Set (Real -> Real)) =
      iInter (fun k => iInter (fun _hkn : k <= n =>
        (cylinder (I k) (L k) : Set (Real -> Real)))) := by
  ext x
  simp only [mem_cylinder, cylinderPrefixBase, Set.mem_setOf_eq,
    Set.mem_iInter]
  rfl


theorem cylinderPrefixBase_isCompact
    (I : Nat -> Finset Real) (L : forall k, Set (I k -> Real))
    (hcompact : forall k, IsCompact (L k)) (n : Nat) :
    IsCompact (cylinderPrefixBase I L n) := by
  classical
  have hclosed : IsClosed (cylinderPrefixBase I L n) := by
    rw [show cylinderPrefixBase I L n =
      iInter (fun k => iInter (fun hkn : k <= n =>
        Finset.restrict₂
          (π := fun _ : Real => Real)
          (cylinderPrefixSupport_subset I hkn) ⁻¹' L k)) by
      ext x
      simp only [cylinderPrefixBase, Set.mem_setOf_eq, Set.mem_iInter,
        Set.mem_preimage]]
    exact isClosed_iInter fun k => isClosed_iInter fun hkn =>
      (hcompact k).isClosed.preimage
        (Finset.continuous_restrict₂ (cylinderPrefixSupport_subset I hkn))
  have hbounded : Bornology.IsBounded (cylinderPrefixBase I L n) := by
    rw [← Bornology.forall_isBounded_image_eval_iff]
    intro q
    have hq : (q : Real) ∈ cylinderPrefixSupport I n := q.property
    change (q : Real) ∈ (Finset.range (n + 1)).biUnion I at hq
    rw [Finset.mem_biUnion] at hq
    obtain ⟨k, hkRange, hqk⟩ := hq
    have hkn : k <= n := by
      rw [Finset.mem_range] at hkRange
      omega
    apply (hcompact k).isBounded.image_eval ⟨q, hqk⟩ |>.subset
    rintro z ⟨x, hx, rfl⟩
    let y : I k -> Real :=
      Finset.restrict₂
        (π := fun _ : Real => Real)
        (cylinderPrefixSupport_subset I hkn) x
    refine ⟨y, hx k hkn, ?_⟩
    rfl
  exact Metric.isCompact_iff_isClosed_bounded.2 ⟨hclosed, hbounded⟩

end StatMech.SLE
