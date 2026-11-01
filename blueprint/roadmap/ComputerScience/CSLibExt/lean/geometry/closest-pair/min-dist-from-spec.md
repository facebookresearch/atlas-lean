---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Geometry.minDistFrom_spec
---

# Min Dist From spec

Two entries at different positions of a list are at different positions of any
permutation, in one order or the other. -/
private theorem pair_sublist_of_perm {l₁ l₂ : List (𝕜 × 𝕜)} {a b : 𝕜 × 𝕜} (hp : l₁ ~ l₂)
    (h : [a, b] <+ l₁) : [a, b] <+ l₂ ∨ [b, a] <+ l₂ := by
  obtain ⟨l, hl, hsub⟩ := List.exists_perm_sublist h hp
  have hlen := hl.length_eq
  match l, hlen, hl, hsub with
  | [x, y], _, hl, hsub =>
      have hx : x ∈ [a, b] := hl.subset List.mem_cons_self
      rcases List.mem_pair.1 hx with rfl | rfl
      · have : [y] ~ [b] := (List.perm_cons x).1 hl
        rw [List.perm_singleton.1 this] at hsub
        exact Or.inl hsub
      · have : [y] ~ [a] := (List.perm_cons x).1 (hl.trans (List.Perm.swap x a []))
        rw [List.perm_singleton.1 this] at hsub
        exact Or.inr hsub

omit [IsStrictOrderedRing 𝕜] in
theorem IsAnswer.perm {l₁ l₂ : List (𝕜 × 𝕜)} {r : Option 𝕜} (h : IsAnswer l₁ r)
    (hp : l₁ ~ l₂) : IsAnswer l₂ r where
  attained δ hδ := by
    obtain ⟨p, q, hpq, hd⟩ := h.attained δ hδ
    rcases pair_sublist_of_perm hp hpq with h' | h'
    · exact ⟨p, q, h', hd⟩
    · exact ⟨q, p, h', by rw [dist2_comm, hd]⟩
  lower p q hpq := by
    rcases pair_sublist_of_perm hp.symm hpq with h' | h'
    · exact h.lower p q h'
    · obtain ⟨δ, hδ, hle⟩ := h.lower q p h'
      exact ⟨δ, hδ, by rwa [dist2_comm]⟩

omit [IsStrictOrderedRing 𝕜] in
theorem IsAnswer.unique {ps : List (𝕜 × 𝕜)} {r r' : Option 𝕜} (h : IsAnswer ps r)
    (h' : IsAnswer ps r') : r = r' := by
  cases r with
  | none =>
      cases r' with
      | none => rfl
      | some δ' =>
          obtain ⟨p, q, hpq, -⟩ := h'.attained δ' rfl
          obtain ⟨δ, hδ, -⟩ := h.lower p q hpq
          simp at hδ
  | some δ =>
      obtain ⟨p, q, hpq, hd⟩ := h.attained δ rfl
      obtain ⟨δ', hδ', hle⟩ := h'.lower p q hpq
      subst hδ'
      obtain ⟨p', q', hpq', hd'⟩ := h'.attained δ' rfl
      obtain ⟨δ'', hδ'', hle'⟩ := h.lower p' q' hpq'
      simp only [Option.some.injEq] at hδ''
      subst hδ''
      exact congrArg some (le_antisymm (hd' ▸ hle') (hd ▸ hle))

omit [IsStrictOrderedRing 𝕜] in
theorem IsAnswer.isMinPairDist2 {ps : List (𝕜 × 𝕜)} {δ : 𝕜} (h : IsAnswer ps (some δ)) :
    IsMinPairDist2 ps δ :=
  ⟨h.attained δ rfl, fun p q hpq => by
    obtain ⟨δ', hδ', hle⟩ := h.lower p q hpq
    simp only [Option.some.injEq] at hδ'
    exact hδ' ▸ hle⟩

/-! ## Brute force

## Depends on

- [Dist2](dist2.md)
- [Min Dist From](min-dist-from.md)

## Proof depends on

- [Omin](../../data-structures/part-03/sparse-table/omin.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Geometry.ClosestPair](../../../../../../sources/v2/CSLibExt.md)
