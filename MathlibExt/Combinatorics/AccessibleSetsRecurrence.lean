/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.AccessibleSets
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Basic

/-!
# Partitioning a set of topological recurrence

If a union of two sets is a set of $k$-topological recurrence, one of the two sets is itself
a set of $k$-topological recurrence.
-/

namespace MetaMathlibExt

namespace topological_recurrence_union_partition

open Set

/-- Compactness gives a lower bound for each descending chain of nonempty closed invariant
sets. A minimal such set carries a minimal homeomorphism by restriction. -/
private theorem exists_minimal_subsystem {X : Type} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (T : X ≃ₜ X) :
    ∃ (K : Set X) (hK : IsClosed K) (hT : K = T ⁻¹' K), K.Nonempty ∧
      @IsMinimalSystem K _ (isCompact_iff_compactSpace.mp hK.isCompact) (T.sets hT) := by
  let family : Set (Set X) := {K | IsClosed K ∧ K.Nonempty ∧ K = T ⁻¹' K}
  have chainBound (c : Set (Set X)) (hc : c ⊆ family) (hc' : IsChain (· ⊆ ·) c)
      (hne : c.Nonempty) : ∃ K ∈ family, ∀ s ∈ c, K ⊆ s := by
    have : Nonempty c := hne.coe_sort
    refine ⟨⋂₀ c, ⟨isClosed_sInter (fun s hs => (hc hs).1), ?_, ?_⟩,
      fun _ hs => sInter_subset_of_mem hs⟩
    · exact IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
        (show IsChain (· ⊇ ·) c from hc'.symm).directedOn (fun _ hs => (hc hs).2.1)
        (fun _ hs => (hc hs).1.isCompact) (fun _ hs => (hc hs).1)
    · ext x
      exact forall₂_congr fun s hs => Set.ext_iff.mp (hc hs).2.2 x
  obtain ⟨K, -, hmin⟩ := zorn_superset_nonempty family chainBound univ
    ⟨isClosed_univ, univ_nonempty, rfl⟩
  obtain ⟨hK, hne, hT⟩ := hmin.prop
  refine ⟨K, hK, hT, hne, ?_⟩
  let R := T.sets hT
  rintro ⟨L, hL, hLne, hproper, hinv⟩
  have himage : T '' (Subtype.val '' L) = Subtype.val '' L := calc
    _ = Subtype.val '' (R '' L) := by rw [image_image, image_image]; rfl
    _ = _ := by rw [show R '' L = L from hinv]
  have hsub : Subtype.val '' L ⊆ K := fun _ ⟨x, _, hx⟩ => hx ▸ x.prop
  have heq := hmin.eq_of_subset
    ⟨hK.isClosedEmbedding_subtypeVal.isClosedMap _ hL, hLne.image _,
      ((Set.preimage_eq_iff_eq_image T.bijective).2 himage.symm).symm⟩ hsub
  apply hproper
  exact eq_univ_of_forall fun x => by
    obtain ⟨y, hy, he⟩ := (show x.val ∈ Subtype.val '' L by rw [heq]; exact x.prop)
    exact Subtype.val_injective he ▸ hy

/-- Every two-sided orbit in a minimal system meets each nonempty open set. -/
private theorem exists_shift {X : Type} [MetricSpace X] [CompactSpace X] (T : X ≃ₜ X)
    (hT : IsMinimalSystem T) {U : Set X} (ho : IsOpen U) (hne : U.Nonempty) (x : X) :
    ∃ n : ℤ, (T ^ n) x ∈ U := by
  let orbit := range fun n : ℤ => (T ^ n) x
  have step (n : ℤ) : T ((T ^ n) x) = (T ^ (n + 1)) x := by
    rw [add_comm, zpow_add, zpow_one, Homeomorph.mul_apply]
  have hinv : T '' orbit = orbit := by
    ext y
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n + 1, (step n).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨_, ⟨n - 1, rfl⟩, by simpa using step (n - 1)⟩
  have hdense : DenseRange (fun n : ℤ => (T ^ n) x) := by
    apply dense_iff_closure_eq.mpr
    by_contra hproper
    exact hT ⟨closure orbit, isClosed_closure, (range_nonempty _).closure, hproper,
      by rw [T.image_closure, hinv]⟩
  exact hdense.exists_mem_open ho hne

/-- A map intertwining the dynamics carries a return in the source open set to a return
with the same gap in the target. -/
private theorem map_return {Z X : Type} [TopologicalSpace Z] [TopologicalSpace X]
    {R : Z ≃ₜ Z} {T : X ≃ₜ X} {f : Z → X} (hf : Function.Semiconj f R T)
    {W : Set Z} {U : Set X} (hWU : MapsTo f W U) {k d : ℕ}
    (hr : (⋂ j : Fin (k + 1), iteratePreimage R (((j : ℕ) : ℤ) * d) W).Nonempty) :
    (⋂ j : Fin (k + 1), iteratePreimage T (((j : ℕ) : ℤ) * d) U).Nonempty := by
  have hpow (n : ℕ) : Function.Semiconj f ⇑(R ^ n) ⇑(T ^ n) := by
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      simp only [pow_succ', Homeomorph.mul_apply, hf.eq, ih.eq]
  obtain ⟨z, hz⟩ := hr
  refine ⟨f z, mem_iInter.mpr fun j => ?_⟩
  have hj := hWU (mem_iInter.mp hz j)
  simpa only [iteratePreimage, mem_preimage, ← Nat.cast_mul, zpow_natCast, (hpow _).eq] using hj

end topological_recurrence_union_partition

open Set topological_recurrence_union_partition

/-- **One part of a union inherits $k$-topological recurrence.** Let $k$ be a natural number
and let $D_1, D_2 \subseteq \mathbb{N}$. If $D_1 \cup D_2$ is a set of $k$-topological recurrence,
then $D_1$ or $D_2$ is a set of $k$-topological recurrence.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Theorem 14. -/
public theorem topological_recurrence_union_partition (k : ℕ)
    (D D₁ D₂ : Set ℕ) (hD : D = D₁ ∪ D₂)
    (hrec : IsLTopologicalRecurrence k D) :
    IsLTopologicalRecurrence k D₁ ∨ IsLTopologicalRecurrence k D₂ := by
  classical
  subst D
  by_cases h₁ : IsLTopologicalRecurrence k D₁
  · exact Or.inl h₁
  have hpos₁ : D₁ ⊆ Ioi 0 := subset_union_left.trans hrec.1
  simp only [IsLTopologicalRecurrence, hpos₁, true_and, not_forall] at h₁
  obtain ⟨X, _, _, T, hT, U, hUo, hUne, hbad⟩ := h₁
  refine Or.inr ⟨Set.Subset.trans Set.subset_union_right hrec.1, ?_⟩
  intro Y _ _ S hS V hVo hVne
  have : Nonempty X := hUne.to_type
  have : Nonempty Y := hVne.to_type
  obtain ⟨K, hK, hinv, ⟨p, hp⟩, hmin⟩ := exists_minimal_subsystem (T.prodCongr S)
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  let R := (T.prodCongr S).sets hinv
  -- Shift the two projections independently so that the same point maps into both open sets.
  obtain ⟨a, ha⟩ := exists_shift T hT hUo hUne p.1
  obtain ⟨b, hb⟩ := exists_shift S hS hVo hVne p.2
  let f (z : K) := (T ^ a) z.val.1
  let g (z : K) := (S ^ b) z.val.2
  let W := f ⁻¹' U ∩ g ⁻¹' V
  have hWo : IsOpen W :=
    (hUo.preimage ((T ^ a).continuous.comp continuous_subtype_val.fst)).inter
      (hVo.preimage ((S ^ b).continuous.comp continuous_subtype_val.snd))
  obtain ⟨d, hd, hr⟩ := hrec.2 K R hmin W hWo ⟨⟨p, hp⟩, ha, hb⟩
  rcases hd with hd | hd
  · have hf : Function.Semiconj f R T := fun z =>
      congrArg (fun H : X ≃ₜ X => H z.val.1) ((Commute.refl T).zpow_left a).eq
    exact (hbad ⟨d, hd, map_return (W := W) hf (fun _ h => h.1) hr⟩).elim
  · have hg : Function.Semiconj g R S := fun z =>
      congrArg (fun H : Y ≃ₜ Y => H z.val.2) ((Commute.refl S).zpow_left b).eq
    exact ⟨d, hd, map_return (W := W) hg (fun _ h => h.2) hr⟩

end MetaMathlibExt
