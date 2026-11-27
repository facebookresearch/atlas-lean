/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).

Adapted from fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2:
Theorems/Thm_Polynomial_irreducible_of_transitive_ringAut.lean and
P2M/Sol/S_Polynomial_irreducible_of_transitive_ringAut.lean, lines 76–177.
The source names no individual authors. The statement and selected proof are
reused with the extraction machinery removed and the public theorem renamed.
-/

module

public import Mathlib.Algebra.Polynomial.Splits

/-!
# Irreducibility from a cycle on all but one root

A monic polynomial splitting with distinct roots is irreducible if one root
lies outside the base field and a base-fixing ring automorphism cycles the
other roots. The automorphism need not act transitively on all the roots;
when there is just one other root, the identity automorphism suffices.
-/

@[expose] public section

/-- A cycle on all roots other than a distinguished nonbase root forces
irreducibility. The enumeration is an exact root multiset, with no repeats. -/
theorem Polynomial.irreducible_of_cycle_on_other_roots
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (P : Polynomial F) (hP : P.Monic)
    (hPs : (P.map (algebraMap F L)).Splits) (σ : L ≃ₐ[F] L)
    (y₀ : L) (r : ℕ → L) (n : ℕ)
    (hroots : (P.map (algebraMap F L)).roots =
      y₀ ::ₘ (Multiset.range n).map r)
    (hnodup : (P.map (algebraMap F L)).roots.Nodup)
    (hcycle : ∀ i < n, σ (r i) = r ((i + 1) % n))
    (hy₀ : y₀ ∉ (algebraMap F L).range) : Irreducible P := by
  classical
  set i := algebraMap F L
  have hσi : (σ.toRingEquiv : L →+* L).comp i = i := RingHom.ext fun a => σ.commutes a
  have hPm0 : P.map i ≠ 0 :=
    (Polynomial.map_ne_zero_iff i.injective).mpr hP.ne_zero
  have hPdeg : P.natDegree = n + 1 := by
    rw [← Polynomial.natDegree_map i, hPs.natDegree_eq_card_roots, hroots,
      Multiset.card_cons, Multiset.card_map, Multiset.card_range]
  have hr_nodup : ((Multiset.range n).map r).Nodup := by
    rw [hroots] at hnodup
    exact (Multiset.nodup_cons.mp hnodup).2
  have key : ∀ f g : Polynomial F, f.Monic → g.Monic → f * g = P →
      y₀ ∈ (f.map i).roots → g.natDegree = 0 := by
    intro f g hf hg hfg hyf
    have hfm0 : f.map i ≠ 0 :=
      (Polynomial.map_ne_zero_iff i.injective).mpr hf.ne_zero
    have hgm0 : g.map i ≠ 0 :=
      (Polynomial.map_ne_zero_iff i.injective).mpr hg.ne_zero
    have hsplit : (P.map i).roots = (f.map i).roots + (g.map i).roots := by
      rw [← hfg, Polynomial.map_mul,
        Polynomial.roots_mul (mul_ne_zero hfm0 hgm0)]
    have hgle : (g.map i).roots ≤ (P.map i).roots := by
      rw [hsplit]
      exact Multiset.le_add_left _ _
    have hy₀g : y₀ ∉ (g.map i).roots := by
      intro hyg
      have h2 : 2 ≤ (P.map i).roots.count y₀ := by
        rw [hsplit, Multiset.count_add]
        have := Multiset.count_pos.mpr hyf
        have := Multiset.count_pos.mpr hyg
        omega
      have h1 := Multiset.nodup_iff_count_le_one.mp hnodup y₀
      omega
    have hgsub : ∀ y ∈ (g.map i).roots, y ∈ (Multiset.range n).map r := by
      intro y hy
      have : y ∈ (P.map i).roots := Multiset.mem_of_le hgle hy
      rw [hroots, Multiset.mem_cons] at this
      rcases this with rfl | h
      · exact absurd hy hy₀g
      · exact h
    have hgs : (g.map i).Splits := Polynomial.Splits.of_dvd hPs hPm0 (by
      rw [← hfg, Polynomial.map_mul]
      exact dvd_mul_left _ _)
    have hstable : ((g.map i).roots).map (σ.toRingEquiv : L →+* L) = (g.map i).roots := by
      rw [← hgs.roots_map (σ.toRingEquiv : L →+* L), Polynomial.map_map, hσi]
    have hmemσ : ∀ y ∈ (g.map i).roots, σ y ∈ (g.map i).roots := by
      intro y hy
      rw [← hstable]
      exact Multiset.mem_map.mpr ⟨y, hy, rfl⟩
    by_contra hgdeg
    have hgroots_ne : (g.map i).roots ≠ 0 := by
      intro h0
      apply hgdeg
      rw [← Polynomial.natDegree_map i, hgs.natDegree_eq_card_roots, h0,
        Multiset.card_zero]
    obtain ⟨y, hy⟩ := Multiset.exists_mem_of_ne_zero hgroots_ne
    obtain ⟨j₀, hj₀, rfl⟩ := Multiset.mem_map.mp (hgsub y hy)
    rw [Multiset.mem_range] at hj₀
    have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hj₀
    have horbit : ∀ k : ℕ, r ((j₀ + k) % n) ∈ (g.map i).roots := by
      intro k
      induction k with
      | zero => rwa [add_zero, Nat.mod_eq_of_lt hj₀]
      | succ k ih =>
        have h1 := hmemσ _ ih
        rw [hcycle _ (Nat.mod_lt _ hnpos), Nat.mod_add_mod, add_assoc] at h1
        exact h1
    have hall : ∀ j < n, r j ∈ (g.map i).roots := by
      intro j hj
      have := horbit (j + n - j₀)
      have e : (j₀ + (j + n - j₀)) % n = j := by
        rw [show j₀ + (j + n - j₀) = j + n by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hj]
      rwa [e] at this
    have hle : (Multiset.range n).map r ≤ (g.map i).roots := by
      rw [Multiset.le_iff_subset hr_nodup]
      intro y hy
      obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp hy
      exact hall j (Multiset.mem_range.mp hj)
    have hgdeg_ge : n ≤ g.natDegree := by
      rw [← Polynomial.natDegree_map i, hgs.natDegree_eq_card_roots]
      simpa using Multiset.card_le_card hle
    have hsum : f.natDegree + g.natDegree = n + 1 := by
      rw [← hf.natDegree_mul hg, hfg, hPdeg]
    have hfdeg_pos : 1 ≤ f.natDegree := by
      rw [← Polynomial.natDegree_map i]
      have := Polynomial.card_roots' (f.map i)
      have hpos : 0 < Multiset.card (f.map i).roots :=
        Multiset.card_pos_iff_exists_mem.mpr ⟨y₀, hyf⟩
      omega
    have hfdeg : f.natDegree = 1 := by omega
    have hfs : f.Splits := Polynomial.Splits.of_natDegree_eq_one hfdeg
    exact hy₀
      (hfs.mem_range_of_isRoot hf.ne_zero ((Polynomial.mem_roots hfm0).mp hyf))
  rw [hP.irreducible_iff_natDegree]
  refine ⟨fun h1 => by simp [h1] at hPdeg, fun f g hf hg hfg => ?_⟩
  have hfm0 : f.map i ≠ 0 :=
    (Polynomial.map_ne_zero_iff i.injective).mpr hf.ne_zero
  have hgm0 : g.map i ≠ 0 :=
    (Polynomial.map_ne_zero_iff i.injective).mpr hg.ne_zero
  have hy₀P : y₀ ∈ (P.map i).roots := by
    rw [hroots]
    exact Multiset.mem_cons_self _ _
  rw [← hfg, Polynomial.map_mul, Polynomial.roots_mul (mul_ne_zero hfm0 hgm0),
    Multiset.mem_add] at hy₀P
  rcases hy₀P with h | h
  · exact Or.inr (key f g hf hg hfg h)
  · exact Or.inl (key g f hg hf (by rw [mul_comm]; exact hfg) h)
