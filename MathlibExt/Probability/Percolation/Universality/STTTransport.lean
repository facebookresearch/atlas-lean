/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Universality.STT

/-!
# Connectivity is preserved by a star–triangle replacement

Let `E` be a graph that does not touch a vertex `O`. Glue onto `E` either a triangle on `A, B, C`
or a star with centre `O` and leaves `A, B, C`, with edge states `ωt` and `ωs` that induce the same
connectivity pattern on `{A, B, C}` (`MatchesPattern ωt ωs`). Then two vertices other than `O` are
connected in `E ⊔ triangle` iff they are connected in `E ⊔ star`. This is the deterministic half
of the star–triangle transformation: combined with the equality of pattern laws in
`MathlibExt.Probability.Percolation.Universality.STT`, it lets one replace triangles by stars
inside a percolation configuration without changing the law of connection events. The coupling
of whole lattices is not constructed here.

## Main definitions

* `StatMech.Universality.triCell`, `StatMech.Universality.starCell`: the open edges of a triangle
  and of a star in a given state.
* `StatMech.Universality.MatchesPattern`: two states induce the same connectivity on the corners.

## Main results

* `StatMech.Universality.bypass_vertex`, `StatMech.Universality.reach_collapse`: two general
  transfer principles for reachability between graphs.
* `StatMech.Universality.starTriangle_reach_iff`: reachability between vertices other than `O` is
  the same after the replacement.

## References

* G. R. Grimmett, I. Manolescu, *Inhomogeneous bond percolation on square, triangular and
  hexagonal lattices*, Ann. Probab. 41 (2013), 2990–3025.
-/

@[expose] public section

open SimpleGraph

namespace StatMech

namespace Universality

variable {V : Type*}

/-- Transfer of reachability avoiding a vertex `O`: if every `G₁`-edge not touching `O` and every
two-step path through `O` can be replaced by a `G₂`-path, then `G₁`-reachability between vertices
other than `O` implies `G₂`-reachability. -/
theorem bypass_vertex (G1 G2 : SimpleGraph V) (O : V)
    (hedge : ∀ a b, a ≠ O → b ≠ O → G1.Adj a b → G2.Reachable a b)
    (hcorner : ∀ s t, s ≠ O → t ≠ O → G1.Adj s O → G1.Adj O t → G2.Reachable s t)
    {u v : V} (hu : u ≠ O) (hv : v ≠ O) (h : G1.Reachable u v) : G2.Reachable u v := by
  obtain ⟨w⟩ := h
  induction n : w.length using Nat.strong_induction_on generalizing u v with
  | _ n IH =>
    subst n
    match w with
    | .nil => exact Reachable.refl _
    | .cons (v := b) hab w' =>
      by_cases hb : b = O
      · match w' with
        | .nil => exact absurd hb hv
        | .cons (v := c) hbc w'' =>
          have hc : c ≠ O := by intro hcO; subst hcO; exact (G1.ne_of_adj hbc) hb
          have hbO : G1.Adj u O := hb ▸ hab
          have hOc : G1.Adj O c := hb ▸ hbc
          exact (hcorner u c hu hc hbO hOc).trans
            (IH w''.length (by simp only [SimpleGraph.Walk.length_cons]; omega) hc hv w'' rfl)
      · exact (hedge u b hu hb hab).trans
          (IH w'.length (by simp only [SimpleGraph.Walk.length_cons]; omega) hb hv w' rfl)

/-- Transfer of reachability along a map `ρ`: if every `G₁`-edge `ab` gives a `G₂`-path from `ρ a`
to `ρ b`, then `G₁`-reachability between fixed points of `ρ` implies `G₂`-reachability. -/
theorem reach_collapse (G1 G2 : SimpleGraph V) (ρ : V → V)
    (hcell : ∀ a b, G1.Adj a b → G2.Reachable (ρ a) (ρ b))
    {u v : V} (hu : ρ u = u) (hv : ρ v = v) (h : G1.Reachable u v) : G2.Reachable u v := by
  obtain ⟨w⟩ := h
  have key : ∀ {x y : V}, (G1.Walk x y) → G2.Reachable (ρ x) (ρ y) := by
    intro x y w
    induction w with
    | nil => exact Reachable.refl _
    | @cons a b c hab w ih => exact (hcell a b hab).trans ih
  have := key w
  rwa [hu, hv] at this

/-- The open edges of the triangle on `A, B, C` in state `ω` (components: `BC`, `AC`, `AB`). -/
def triCell (A B C : V) (ω : LocalConfig) : SimpleGraph V :=
  fromEdgeSet { e | (ω.1 ∧ e = s(B, C)) ∨ (ω.2.1 ∧ e = s(A, C)) ∨ (ω.2.2 ∧ e = s(A, B)) }

/-- The open edges of the star with centre `O` and leaves `A, B, C` in state `ω`
(components: `OA`, `OB`, `OC`). -/
def starCell (A B C O : V) (ω : LocalConfig) : SimpleGraph V :=
  fromEdgeSet { e | (ω.1 ∧ e = s(O, A)) ∨ (ω.2.1 ∧ e = s(O, B)) ∨ (ω.2.2 ∧ e = s(O, C)) }

theorem triCell_adj_BC (A B C : V) (ω : LocalConfig) (h : ω.1 = true) (hBC : B ≠ C) :
    (triCell A B C ω).Adj B C := by
  unfold triCell; rw [fromEdgeSet_adj]; exact ⟨Or.inl ⟨h, rfl⟩, hBC⟩

theorem triCell_adj_AC (A B C : V) (ω : LocalConfig) (h : ω.2.1 = true) (hAC : A ≠ C) :
    (triCell A B C ω).Adj A C := by
  unfold triCell; rw [fromEdgeSet_adj]; exact ⟨Or.inr (Or.inl ⟨h, rfl⟩), hAC⟩

theorem triCell_adj_AB (A B C : V) (ω : LocalConfig) (h : ω.2.2 = true) (hAB : A ≠ B) :
    (triCell A B C ω).Adj A B := by
  unfold triCell; rw [fromEdgeSet_adj]; exact ⟨Or.inr (Or.inr ⟨h, rfl⟩), hAB⟩

/-- An edge of `triCell` is one of the three sides, open in `ω`. -/
theorem triCell_adj_imp (A B C : V) (ω : LocalConfig) {x y : V}
    (h : (triCell A B C ω).Adj x y) :
    (ω.1 ∧ s(x, y) = s(B, C)) ∨ (ω.2.1 ∧ s(x, y) = s(A, C)) ∨ (ω.2.2 ∧ s(x, y) = s(A, B)) := by
  unfold triCell at h
  rw [fromEdgeSet_adj] at h
  simpa using h.1

theorem starCell_adj_OA (A B C O : V) (ω : LocalConfig) (h : ω.1 = true) (hOA : O ≠ A) :
    (starCell A B C O ω).Adj O A := by
  unfold starCell; rw [fromEdgeSet_adj]; exact ⟨Or.inl ⟨h, rfl⟩, hOA⟩

theorem starCell_adj_OB (A B C O : V) (ω : LocalConfig) (h : ω.2.1 = true) (hOB : O ≠ B) :
    (starCell A B C O ω).Adj O B := by
  unfold starCell; rw [fromEdgeSet_adj]; exact ⟨Or.inr (Or.inl ⟨h, rfl⟩), hOB⟩

theorem starCell_adj_OC (A B C O : V) (ω : LocalConfig) (h : ω.2.2 = true) (hOC : O ≠ C) :
    (starCell A B C O ω).Adj O C := by
  unfold starCell; rw [fromEdgeSet_adj]; exact ⟨Or.inr (Or.inr ⟨h, rfl⟩), hOC⟩

/-- An edge of `starCell` joins `O` to a leaf whose spoke is open in `ω`. -/
theorem starCell_adj_imp (A B C O : V) (ω : LocalConfig) {x y : V}
    (h : (starCell A B C O ω).Adj x y) :
    (x = O ∧ ((y = A ∧ ω.1) ∨ (y = B ∧ ω.2.1) ∨ (y = C ∧ ω.2.2))) ∨
    (y = O ∧ ((x = A ∧ ω.1) ∨ (x = B ∧ ω.2.1) ∨ (x = C ∧ ω.2.2))) := by
  unfold starCell at h
  rw [fromEdgeSet_adj] at h
  obtain ⟨hmem, _⟩ := h
  simp only [Set.mem_ofPred_eq] at hmem
  rcases hmem with ⟨hb, he⟩ | ⟨hb, he⟩ | ⟨hb, he⟩ <;>
    rw [Sym2.eq_iff] at he <;> rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all

variable (E : SimpleGraph V)

/-- If the triangle connects `B` and `C`, they are reachable in `E ⊔ triCell`. -/
theorem triCell_reach_BC (A B C : V) (ω : LocalConfig)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (h : triBC ω = true) :
    (E ⊔ triCell A B C ω).Reachable B C := by
  unfold triBC at h; rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact Adj.reachable (Or.inr (triCell_adj_BC A B C ω h hBC))
  · rw [Bool.and_eq_true] at h
    exact (Adj.reachable (Or.inr (triCell_adj_AB A B C ω h.2 hAB))).symm.trans
      (Adj.reachable (Or.inr (triCell_adj_AC A B C ω h.1 hAC)))

/-- If the triangle connects `A` and `C`, they are reachable in `E ⊔ triCell`. -/
theorem triCell_reach_AC (A B C : V) (ω : LocalConfig)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (h : triAC ω = true) :
    (E ⊔ triCell A B C ω).Reachable A C := by
  unfold triAC at h; rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact Adj.reachable (Or.inr (triCell_adj_AC A B C ω h hAC))
  · rw [Bool.and_eq_true] at h
    exact (Adj.reachable (Or.inr (triCell_adj_AB A B C ω h.2 hAB))).trans
      (Adj.reachable (Or.inr (triCell_adj_BC A B C ω h.1 hBC)))

/-- If the triangle connects `A` and `B`, they are reachable in `E ⊔ triCell`. -/
theorem triCell_reach_AB (A B C : V) (ω : LocalConfig)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (h : triAB ω = true) :
    (E ⊔ triCell A B C ω).Reachable A B := by
  unfold triAB at h; rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact Adj.reachable (Or.inr (triCell_adj_AB A B C ω h hAB))
  · rw [Bool.and_eq_true] at h
    exact (Adj.reachable (Or.inr (triCell_adj_AC A B C ω h.2 hAC))).trans
      (Adj.reachable (Or.inr (triCell_adj_BC A B C ω h.1 hBC))).symm

/-- If the star connects `A` and `B`, they are reachable in `E ⊔ starCell`. -/
theorem starCell_reach_AB (A B C O : V) (ω : LocalConfig)
    (hOA : O ≠ A) (hOB : O ≠ B) (h : starAB ω = true) :
    (E ⊔ starCell A B C O ω).Reachable A B := by
  unfold starAB at h; rw [Bool.and_eq_true] at h
  exact (Adj.reachable (Or.inr (starCell_adj_OA A B C O ω h.1 hOA))).symm.trans
    (Adj.reachable (Or.inr (starCell_adj_OB A B C O ω h.2 hOB)))

/-- If the star connects `A` and `C`, they are reachable in `E ⊔ starCell`. -/
theorem starCell_reach_AC (A B C O : V) (ω : LocalConfig)
    (hOA : O ≠ A) (hOC : O ≠ C) (h : starAC ω = true) :
    (E ⊔ starCell A B C O ω).Reachable A C := by
  unfold starAC at h; rw [Bool.and_eq_true] at h
  exact (Adj.reachable (Or.inr (starCell_adj_OA A B C O ω h.1 hOA))).symm.trans
    (Adj.reachable (Or.inr (starCell_adj_OC A B C O ω h.2 hOC)))

/-- If the star connects `B` and `C`, they are reachable in `E ⊔ starCell`. -/
theorem starCell_reach_BC (A B C O : V) (ω : LocalConfig)
    (hOB : O ≠ B) (hOC : O ≠ C) (h : starBC ω = true) :
    (E ⊔ starCell A B C O ω).Reachable B C := by
  unfold starBC at h; rw [Bool.and_eq_true] at h
  exact (Adj.reachable (Or.inr (starCell_adj_OB A B C O ω h.1 hOB))).symm.trans
    (Adj.reachable (Or.inr (starCell_adj_OC A B C O ω h.2 hOC)))

/-- The triangle state `ωt` and the star state `ωs` connect the same pairs of corners. -/
def MatchesPattern (ωt ωs : LocalConfig) : Prop :=
  triAB ωt = starAB ωs ∧ triAC ωt = starAC ωs ∧ triBC ωt = starBC ωs

/-- Reachability in `E ⊔ triangle` implies reachability in `E ⊔ star` for matching states. -/
theorem reach_tri_to_star (A B C O : V) (ωt ωs : LocalConfig)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hOA : O ≠ A) (hOB : O ≠ B) (hOC : O ≠ C)
    (hm : MatchesPattern ωt ωs) {u v : V}
    (h : (E ⊔ triCell A B C ωt).Reachable u v) :
    (E ⊔ starCell A B C O ωs).Reachable u v := by
  obtain ⟨hmAB, hmAC, hmBC⟩ := hm
  refine reach_collapse _ _ id ?_ rfl rfl h
  intro a b hab
  simp only [id]
  rcases hab with hE | hcell
  · exact Adj.reachable (Or.inl hE)
  · rcases triCell_adj_imp A B C ωt hcell with ⟨hb, he⟩ | ⟨hb, he⟩ | ⟨hb, he⟩
    · have hstar : starBC ωs = true := by
        rw [← hmBC]; unfold triBC; simp [hb]
      have r := starCell_reach_BC E A B C O ωs hOB hOC hstar
      rw [Sym2.eq_iff] at he
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact r
      · exact r.symm
    · have hstar : starAC ωs = true := by
        rw [← hmAC]; unfold triAC; simp [hb]
      have r := starCell_reach_AC E A B C O ωs hOA hOC hstar
      rw [Sym2.eq_iff] at he
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact r
      · exact r.symm
    · have hstar : starAB ωs = true := by
        rw [← hmAB]; unfold triAB; simp [hb]
      have r := starCell_reach_AB E A B C O ωs hOA hOB hstar
      rw [Sym2.eq_iff] at he
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact r
      · exact r.symm

/-- Reachability in `E ⊔ star` between vertices other than `O` implies reachability in
`E ⊔ triangle`, provided `E` has no edge at `O`. -/
theorem reach_star_to_tri (A B C O : V) (ωt ωs : LocalConfig)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hOA : O ≠ A) (hOB : O ≠ B) (hOC : O ≠ C)
    (hm : MatchesPattern ωt ωs)
    (hEO : ∀ x, ¬ E.Adj x O) {u v : V} (hu : u ≠ O) (hv : v ≠ O)
    (h : (E ⊔ starCell A B C O ωs).Reachable u v) :
    (E ⊔ triCell A B C ωt).Reachable u v := by
  obtain ⟨hmAB, hmAC, hmBC⟩ := hm
  have triAB' : starAB ωs = true → (E ⊔ triCell A B C ωt).Reachable A B := fun hs =>
    triCell_reach_AB E A B C ωt hAB hAC hBC (by rw [hmAB]; exact hs)
  have triAC' : starAC ωs = true → (E ⊔ triCell A B C ωt).Reachable A C := fun hs =>
    triCell_reach_AC E A B C ωt hAB hAC hBC (by rw [hmAC]; exact hs)
  have triBC' : starBC ωs = true → (E ⊔ triCell A B C ωt).Reachable B C := fun hs =>
    triCell_reach_BC E A B C ωt hAB hAC hBC (by rw [hmBC]; exact hs)
  refine bypass_vertex _ _ O ?_ ?_ hu hv h
  · intro a b ha hb hab
    rcases hab with hE | hcell
    · exact Adj.reachable (Or.inl hE)
    · rcases starCell_adj_imp A B C O ωs hcell with ⟨hO, _⟩ | ⟨hO, _⟩
      · exact absurd hO ha
      · exact absurd hO hb
  · intro s t hs ht hsO hOt
    have hspoke : ∀ {p : V}, (E ⊔ starCell A B C O ωs).Adj p O → p ≠ O →
        (p = A ∧ ωs.1 = true) ∨ (p = B ∧ ωs.2.1 = true) ∨ (p = C ∧ ωs.2.2 = true) := by
      intro p hpO hpne
      rcases hpO with hE | hcell
      · exact absurd hE (hEO p)
      · rcases starCell_adj_imp A B C O ωs hcell with ⟨hO, _⟩ | ⟨_, hcase⟩
        · exact absurd hO hpne
        · rcases hcase with ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩
          · exact Or.inl ⟨rfl, hb⟩
          · exact Or.inr (Or.inl ⟨rfl, hb⟩)
          · exact Or.inr (Or.inr ⟨rfl, hb⟩)
    have hsp_s := hspoke hsO hs
    have hsp_t := hspoke hOt.symm ht
    rcases hsp_s with ⟨rfl, hsb⟩ | ⟨rfl, hsb⟩ | ⟨rfl, hsb⟩ <;>
      rcases hsp_t with ⟨rfl, htb⟩ | ⟨rfl, htb⟩ | ⟨rfl, htb⟩
    · exact Reachable.refl _
    · exact triAB' (by unfold starAB; simp [hsb, htb])
    · exact triAC' (by unfold starAC; simp [hsb, htb])
    · exact (triAB' (by unfold starAB; simp [hsb, htb])).symm
    · exact Reachable.refl _
    · exact triBC' (by unfold starBC; simp [hsb, htb])
    · exact (triAC' (by unfold starAC; simp [hsb, htb])).symm
    · exact (triBC' (by unfold starBC; simp [hsb, htb])).symm
    · exact Reachable.refl _

/-- Star–triangle replacement preserves reachability between vertices other than the star centre,
when the two cells induce the same connectivity pattern and `E` has no edge at the centre. -/
theorem starTriangle_reach_iff (A B C O : V) (ωt ωs : LocalConfig)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hOA : O ≠ A) (hOB : O ≠ B) (hOC : O ≠ C)
    (hm : MatchesPattern ωt ωs) (hEO : ∀ x, ¬ E.Adj x O) {u v : V} (hu : u ≠ O) (hv : v ≠ O) :
    (E ⊔ triCell A B C ωt).Reachable u v ↔ (E ⊔ starCell A B C O ωs).Reachable u v :=
  ⟨reach_tri_to_star E A B C O ωt ωs hAB hAC hBC hOA hOB hOC hm,
   reach_star_to_tri E A B C O ωt ωs hAB hAC hBC hOA hOB hOC hm hEO hu hv⟩

/-- `starTriangle_reach_iff` stated for the endpoints `u`, `v` given as existentials. -/
theorem starTriangle_crossing_transport (A B C O : V) (ωt ωs : LocalConfig)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hOA : O ≠ A) (hOB : O ≠ B) (hOC : O ≠ C)
    (hm : MatchesPattern ωt ωs) (hEO : ∀ x, ¬ E.Adj x O) {u v : V} (hu : u ≠ O) (hv : v ≠ O) :
    (∃ p q : V, p = u ∧ q = v ∧ (E ⊔ triCell A B C ωt).Reachable p q) ↔
    (∃ p q : V, p = u ∧ q = v ∧ (E ⊔ starCell A B C O ωs).Reachable p q) := by
  constructor
  · rintro ⟨p, q, rfl, rfl, hpq⟩
    exact ⟨p, q, rfl, rfl,
      (starTriangle_reach_iff E A B C O ωt ωs hAB hAC hBC hOA hOB hOC hm hEO hu hv).1 hpq⟩
  · rintro ⟨p, q, rfl, rfl, hpq⟩
    exact ⟨p, q, rfl, rfl,
      (starTriangle_reach_iff E A B C O ωt ωs hAB hAC hBC hOA hOB hOC hm hEO hu hv).2 hpq⟩

end Universality

end StatMech
