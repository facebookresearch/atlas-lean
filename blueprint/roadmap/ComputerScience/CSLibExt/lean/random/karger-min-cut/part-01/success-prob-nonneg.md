---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Karger.successProb_nonneg
---

# Success Prob nonneg

Every vertex has degree at least the minimum cut size, so `n k ≤ 2 |E|`. -/
theorem card_mul_le_two_mul_edges {st : State V} (hv : st.Valid) {k : ℕ} (hmin : IsMinCut st k)
    (hn : 2 ≤ st.verts.length) : st.verts.length * k ≤ 2 * st.edges.length := by
  classical
  rw [← sum_degree st hv]
  refine length_mul_le_sum k _ st.verts fun v hv' => ?_
  refine hmin.2 _ ⟨⟨v, hv', by simp⟩, ?_⟩
  obtain ⟨w, hw, hwv⟩ : ∃ w ∈ st.verts, w ≠ v := by
    by_contra hcon
    push Not at hcon
    have : st.verts = List.replicate st.verts.length v :=
      List.eq_replicate_iff.2 ⟨rfl, hcon⟩
    have hnd := hv.1
    rw [this] at hnd
    have := List.nodup_replicate.1 hnd
    omega
  exact ⟨w, hw, by simp [hwv]⟩

/-! ## The success probability

## Depends on

- [State](state.md)
- [Success Prob](success-prob.md)

## Proof depends on

- [Contract](contract.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Random.KargerMinCut](../../../../../../../sources/v2/CSLibExt.md)
