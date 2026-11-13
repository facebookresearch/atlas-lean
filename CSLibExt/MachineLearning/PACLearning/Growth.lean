/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.MachineLearning.PACLearning.VCDimension

/-!
# Finite traces of a concept class

Traces are positive subsets of the sample subtype, not hypotheses. Thus
hypotheses agreeing on the sample contribute only one trace. The mathematical
family works for arbitrary classes; `finiteTraces` computes it for a list of
hypotheses without deciding equality of functions or membership in an
arbitrary concept class.
-/

@[expose] public section

namespace Cslib.MachineLearning.PACLearning

variable {α : Type*}

open scoped Classical in
/-- The distinct positive subsets realized by `C` on the finite sample `s`.
Using the sample subtype excludes all labels outside the sample. -/
noncomputable def traceFamily (C : ConceptClass α Bool) (s : Finset α) :
    Finset (Finset s) :=
  Finset.univ.filter fun t =>
    ∃ c ∈ C, ∀ x : s, x ∈ t ↔ c x = true

/-- A trace is exactly the positive labeling of some concept in `C`. -/
@[simp] theorem mem_traceFamily {C : ConceptClass α Bool} {s : Finset α}
    {t : Finset s} :
    t ∈ traceFamily C s ↔ ∃ c ∈ C, ∀ x : s, x ∈ t ↔ c x = true := by
  classical
  simp [traceFamily]

/-- Enumerate distinct sample traces of a finite list of hypotheses.
Only equality of sample points is decided; functions are never compared. -/
def finiteTraces [DecidableEq α] (H : List (α → Bool)) (s : Finset α) :
    Finset (Finset s) :=
  (H.map fun c => Finset.univ.filter fun x : s => c x = true).toFinset

/-- The executable enumeration represents the mathematical trace family of
the class given by list membership, including repeated hypotheses. -/
theorem finiteTraces_eq_traceFamily [DecidableEq α]
    (H : List (α → Bool)) (s : Finset α) :
    finiteTraces H s = traceFamily {c | c ∈ H} s := by
  classical
  ext t
  simp only [finiteTraces, List.mem_toFinset, List.mem_map, mem_traceFamily,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, fun x => by simp⟩
  · rintro ⟨c, hc, ht⟩
    exact ⟨c, hc, Finset.ext fun x => by simpa using (ht x).symm⟩

private theorem setShatters_of_shatters_traceFamily [DecidableEq α]
    {C : ConceptClass α Bool} {s : Finset α} {t : Finset s}
    (h : (traceFamily C s).Shatters t) :
    SetShatters C (Subtype.val '' (t : Set s)) := by
  intro W hW
  have h' : @Finset.Shatters s (Classical.decEq s) (traceFamily C s) t := by
    convert h using 1
  obtain ⟨g, ⟨u, hu, hgu⟩, hg⟩ := h'.toSetShatters
    (Subtype.val ⁻¹' W) (by
      rintro x hx
      obtain ⟨y, hy, hyx⟩ := hW hx
      exact Subtype.val_injective hyx ▸ hy)
  obtain ⟨c, hc, hcu⟩ := mem_traceFamily.mp hu
  have hx (x : s) : (c x = true ∧ x ∈ t) ↔ x.val ∈ W := by
    have hx := Set.ext_iff.mp hg x
    simpa only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Finset.mem_coe, hgu, decide_eq_true_eq, hcu] using hx
  refine ⟨c, hc, Set.ext fun a => ?_⟩
  constructor
  · rintro ⟨hca, x, hxt, rfl⟩
    exact (hx x).mp ⟨hca, hxt⟩
  · intro ha
    obtain ⟨x, hxt, rfl⟩ := hW ha
    exact ⟨((hx x).mpr ha).1, x, hxt, rfl⟩

/-- Shattering traces is equivalent to canonical shattering of the same
sample points in the original domain. -/
theorem shatters_traceFamily_iff [DecidableEq α]
    {C : ConceptClass α Bool} {s : Finset α}
    {t : Finset s} :
    (traceFamily C s).Shatters t ↔
      SetShatters C (Subtype.val '' (t : Set s)) := by
  refine ⟨setShatters_of_shatters_traceFamily, fun h u hu => ?_⟩
  obtain ⟨c, hc, hcu⟩ := h (Subtype.val '' (u : Set s))
    (Set.image_mono hu)
  refine ⟨Finset.univ.filter (fun x : s => c x = true),
    mem_traceFamily.mpr ⟨c, hc, fun x => by simp⟩, ?_⟩
  ext x
  have hx := Set.ext_iff.mp hcu x.val
  simpa only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
    true_and, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
    Set.mem_image, Subtype.val_inj, exists_eq_right, exists_eq_left,
    Finset.mem_coe, and_comm] using hx

/-- Restricting a finite-VC class to a finite sample cannot increase its
canonical VC dimension. Boundedness is needed for `le_csSup` on `ℕ`. -/
theorem vcDim_traceFamily_le [DecidableEq α] {C : ConceptClass α Bool}
    (hC : HasFiniteVCDim C) (s : Finset α) :
    (traceFamily C s).vcDim ≤ vcDim C := by
  apply Finset.sup_le
  intro t ht
  have ht' : SetShatters C ↑(t.image Subtype.val) := by
    simpa only [Finset.coe_image] using
      shatters_traceFamily_iff.mp (Finset.mem_shatterer.mp ht)
  have h := le_csSup hC ⟨t.image Subtype.val, rfl, ht'⟩
  simpa only [vcDim,
    Finset.card_image_of_injective t Subtype.val_injective] using h

/-- The finite-sample Sauer-Shelah bound for CSLib's canonical concept class
and VC dimension. The finite-VC premise is essential: the `ℕ` supremum used
by `vcDim` is zero for unbounded shattered sizes. This is a combinatorial
growth bound, not a probabilistic sample-complexity theorem. -/
theorem card_traceFamily_le_sum_vcDim {C : ConceptClass α Bool}
    (hC : HasFiniteVCDim C) (s : Finset α) :
    (traceFamily C s).card ≤
      ∑ k ∈ Finset.Iic (vcDim C), s.card.choose k := by
  classical
  calc
    (traceFamily C s).card ≤ (traceFamily C s).shatterer.card :=
      Finset.card_le_card_shatterer _
    _ ≤ ∑ k ∈ Finset.Iic (traceFamily C s).vcDim,
        (Fintype.card s).choose k := Finset.card_shatterer_le_sum_vcDim
    _ ≤ ∑ k ∈ Finset.Iic (vcDim C), (Fintype.card s).choose k :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Iic_subset_Iic.mpr (vcDim_traceFamily_le hC s))
        (fun _ _ _ => Nat.zero_le _)
    _ = _ := by rw [Fintype.card_coe]

end Cslib.MachineLearning.PACLearning
