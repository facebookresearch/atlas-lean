/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.SnortOppositions
public import MathlibExt.GraphTheory.SnortOppositionsExistsLargeTreeSnortSecondPlayerWins
import all MathlibExt.GraphTheory.SnortOppositionsExistsLargeTreeSnortSecondPlayerWins

/-!
# The opposition strategy in Snort

The second player answers each move by its image under the opposition. The two occupied sets
are therefore images of each other at the start of each first-player turn.

## References

* Rylo Ashmore, Beth Ann Austin, Alfie M. Davies, Danny Dyer, and William Kellough,
  *On Graph Automorphisms Related to SNORT*, INTEGERS 26 (2026), Article G2, pp. 1–28,
  Lemma 1 (§2, p. 4).
* Keiko Kakihara, *Snort: A combinatorial game*, Master's thesis, California State University,
  San Bernardino, 2010, Proposition 3.6 (p. 24), cited by Ashmore et al. They note that Kakihara
  credits a preprint by Stacey Stokes and Mark D. Schlatter that they could not locate.
-/

namespace MetaMathlibExt

variable {V : Type*}

private theorem snortMoverWins_eq_false_of_mirrored [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {f : G ≃g G} (hf : IsOpposition G f)
    (k : ℕ) (A B : Finset V) (hB : B = A.image f)
    (hbudget : Fintype.card V ≤ k + (A ∪ B).card) : snortMoverWins G k A B = false := by
  induction k using Nat.strong_induction_on generalizing A B with
  | ind k ih =>
    cases k with
    | zero => rfl
    | succ k =>
      apply (losing_iff G k A B).mpr
      intro v hvA hvB hvAdj
      have hvImage (w : V) (hw : w ∈ A) : f w ∈ B := hB ▸ Finset.mem_image_of_mem f hw
      have hwA : f v ∉ A := fun hw => hvB ((hf v).1 ▸ hvImage (f v) hw)
      have hwB : f v ∉ B := by
        rw [hB]
        intro hw
        obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hw
        exact hvA (f.injective heq ▸ hw)
      have hwAdj (w : V) (hw : w ∈ A) : ¬ G.Adj (f v) w := by
        intro hadj
        have hmap : G.Adj (f (f v)) (f w) := f.map_adj_iff.mpr hadj
        exact hvAdj (f w) (hvImage w hw) ((hf v).1 ▸ hmap)
      have hw := legal_after G A B v (f v) (show Legal G B A (f v) from ⟨hwB, hwA, hwAdj⟩)
        (hf v).2.1 (fun hadj => (hf v).2.2 hadj.symm)
      have hcard : (insert v A ∪ insert (f v) B).card = (A ∪ B).card + 2 := by
        rw [colored_card_insert B (insert v A) (f v) hw.1 hw.2.1,
          colored_card_insert A B v hvA hvB]
      cases k with
      | zero =>
        -- The legal reply needs a second free vertex, so the budget cannot be one.
        have hle := Finset.card_le_univ (insert v A ∪ insert (f v) B)
        omega
      | succ k =>
        apply (winning_iff G k B (insert v A)).mpr
        refine ⟨f v, hw.1, hw.2.1, hw.2.2, ?_⟩
        apply ih k (by omega) (insert v A) (insert (f v) B)
        · rw [Finset.image_insert, ← hB]
        · omega

/-- **The second player wins Snort on opposable graphs.** If a finite simple graph $G$ is
opposable, then the second player wins Snort on $G$.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Lemma 1 (Kakihara,
Proposition 3.6). -/
public theorem snortSecondPlayerWins_of_isOpposable [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : IsOpposable G) : SnortSecondPlayerWins G := by
  obtain ⟨f, hf⟩ := h
  exact snortMoverWins_eq_false_of_mirrored G hf (Fintype.card V) ∅ ∅ (by simp) (by simp)

end MetaMathlibExt
