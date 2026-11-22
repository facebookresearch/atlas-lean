/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang
-/
module

public import MathlibExt.SetTheory.Forcing.ForcingAxioms.MartinAxiom
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Order.PFilter
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Basic

@[expose] public section

/-! Restated here so this file is self-contained: `IsCCC` matches `SetTheory.lean`, and
`IsSigmaCentered` / `IsSigmaCentered.isCCC` match `SetTheory/SigmaCenter_sanity.lean`,
`MartinAxiom` matches `SetTheory/MartinAxiom_sanity.lean`. -/

open Set

namespace MathlibExtTest.SetTheory.Forcing.ForcingAxioms.MartinAxiom

open MetaMathlibExt

-- Logic 10: Countable chain condition in a partial order

/-- Three cases pinning down the definition.

The first two use the same underlying poset — subsets of `ℝ` ordered by `⊆` — and differ only
by whether the zero condition `∅` is present.  With `∅` every pair has a common lower bound,
so the antichains are subsingletons; without it the singletons are pairwise incompatible and
there are continuum many.  Together they check that "antichain" means pairwise *incompatible*
rather than pairwise incomparable — under the latter reading the first case would be false,
since `(P(ℝ), ⊆)` has incomparable families of size continuum — and that the definition is not
vacuously true.

The third case exercises the `Countable` conclusion itself.  Nonempty subsets of `ℕ` under `⊆`
have no bottom element, so this is not the trivial case; antichains there are pairwise disjoint
families, hence countable, yet the singletons form an infinite one.  Without this case the
statement would still hold with `A.Countable` weakened to `A.Subsingleton`, which is not ccc
but rather "no two elements are incompatible". -/

theorem isCCC_sanity :
    IsCCC (Set ℝ) ∧ ¬ IsCCC {s : Set ℝ // s.Nonempty} ∧
      (IsCCC {s : Set ℕ // s.Nonempty} ∧
        ∃ A : Set {s : Set ℕ // s.Nonempty},
          IsAntichain (fun p q : {s : Set ℕ // s.Nonempty} => ∃ r, r ≤ p ∧ r ≤ q) A ∧
            A.Infinite) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `∅` is a common lower bound, so antichains are subsingletons.
    intro A hA
    refine Set.Subsingleton.countable fun p hp q hq => ?_
    by_contra hne
    exact hA hp hq hne ⟨⊥, bot_le, bot_le⟩
  · -- Without `∅`, the singletons are pairwise incompatible and there are uncountably many.
    intro hccc
    set f : ℝ → {s : Set ℝ // s.Nonempty} := fun x => ⟨{x}, Set.singleton_nonempty x⟩
    have hinj : Function.Injective f := by
      intro x y hxy
      have h : ({x} : Set ℝ) = {y} := congrArg Subtype.val hxy
      simpa using h
    have hanti : IsAntichain (fun p q : {s : Set ℝ // s.Nonempty} => ∃ r, r ≤ p ∧ r ≤ q)
        (Set.range f) := by
      rintro p ⟨x, rfl⟩ q ⟨y, rfl⟩ hne ⟨⟨t, htne⟩, h1, h2⟩
      obtain ⟨z, hz⟩ := htne
      exact hne (congrArg f ((h1 hz : z = x).symm.trans (h2 hz : z = y)))
    have hcount := (hccc _ hanti).preimage hinj
    rw [Set.preimage_range] at hcount
    exact Cardinal.not_countable_real hcount
  · -- Incompatible nonempty subsets of `ℕ` are disjoint, so an antichain injects into `ℕ`.
    intro A hA
    rw [Set.countable_iff_exists_injOn]
    refine ⟨fun p => p.2.some, fun p hp q hq hpq => ?_⟩
    have hpq' : p.2.some = q.2.some := hpq
    by_contra hne
    refine hA hp hq hne ⟨⟨{p.2.some}, Set.singleton_nonempty _⟩, ?_, ?_⟩
    · exact Set.singleton_subset_iff.2 p.2.some_mem
    · exact Set.singleton_subset_iff.2 (by rw [hpq']; exact q.2.some_mem)
  · -- ... but that antichain may still be infinite: take the singletons.
    refine ⟨Set.range (fun n : ℕ => (⟨{n}, Set.singleton_nonempty n⟩ :
      {s : Set ℕ // s.Nonempty})), ?_, ?_⟩
    · rintro p ⟨n, rfl⟩ q ⟨m, rfl⟩ hne ⟨⟨t, htne⟩, h1, h2⟩
      obtain ⟨z, hz⟩ := htne
      exact hne (by simp [(h1 hz : z = n).symm.trans (h2 hz : z = m)])
    · refine Set.infinite_range_of_injective fun n m hnm => ?_
      simpa [Subtype.ext_iff] using hnm

-- Logic 13: $\sigma$-centered posets

theorem _root_.MetaMathlibExt.IsSigmaCentered.nonempty {P : Type*} [PartialOrder P] (h : IsSigmaCentered P) :
    Nonempty P := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨r, -⟩ := hc 0 ∅ (by simp)
  exact ⟨r⟩

/-- Validity: σ-centered implies ccc, the standard first fact about the notion.

Two elements sharing a colour are compatible, so an antichain meets each colour class at most
once and therefore injects into `ℕ`.  This is the sanity check with the most content: it ties
`IsSigmaCentered` to the independently-stated `IsCCC` and would break if the centeredness
clause asked for an *upper* bound, or if `c` landed in an uncountable index type. -/

theorem _root_.MetaMathlibExt.IsSigmaCentered.isCCC {P : Type*} [PartialOrder P] (h : IsSigmaCentered P) :
    IsCCC P := by
  classical
  obtain ⟨c, hc⟩ := h
  intro A hA
  rw [Set.countable_iff_exists_injOn]
  refine ⟨c, fun p hp q hq hpq => ?_⟩
  by_contra hne
  obtain ⟨r, hr⟩ := hc (c p) {p, q} (by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · rfl
    · exact hpq.symm)
  exact hA hp hq hne ⟨r, hr p (by simp), hr q (by simp)⟩

/-- Nonvacuous, with the colouring doing real work: every countable nonempty poset is
σ-centered, by giving each element its own colour.  No order-theoretic hypothesis is needed,
which is exactly the classical fact. -/

theorem isSigmaCentered_of_countable {P : Type*} [PartialOrder P] [Countable P] [Nonempty P] :
    IsSigmaCentered P := by
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat P
  refine ⟨f, fun n s hs => ?_⟩
  rcases s.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · exact ⟨Classical.arbitrary P, by simp⟩
  · refine ⟨p₀, fun p hp => ?_⟩
    have hfp : f p = f p₀ := by rw [hs p hp, hs p₀ hp₀]
    exact le_of_eq (hf hfp).symm

/-- Sanity check for `IsSigmaCentered`, bracketing the definition from both sides.

1. **Satisfiable by something uncountable.** `(P(ℝ), ⊆)` is σ-centered via the constant
   colouring, since `∅` bounds everything.  Together with `isSigmaCentered_of_countable` this
   shows the notion is not secretly "countable" and not secretly "has a bottom element".
2. **Not trivially true.** Nonempty subsets of `ℝ` under `⊆` are not σ-centered.  This is
   derived from `IsSigmaCentered.isCCC`: that poset is not even ccc, because the singletons
   form an antichain of size continuum. -/

theorem isSigmaCentered_sanity :
    IsSigmaCentered (Set ℝ) ∧ ¬ IsSigmaCentered {s : Set ℝ // s.Nonempty} := by
  constructor
  · exact ⟨fun _ => 0, fun _ _ _ => ⟨⊥, fun _ _ => bot_le⟩⟩
  · -- The singletons are pairwise incompatible and there are uncountably many of them.
    intro hσ
    have hccc : IsCCC {s : Set ℝ // s.Nonempty} := hσ.isCCC
    set f : ℝ → {s : Set ℝ // s.Nonempty} := fun x => ⟨{x}, Set.singleton_nonempty x⟩
    have hinj : Function.Injective f := by
      intro x y hxy
      have h : ({x} : Set ℝ) = {y} := congrArg Subtype.val hxy
      simpa using h
    have hanti : IsAntichain (fun p q : {s : Set ℝ // s.Nonempty} => ∃ r, r ≤ p ∧ r ≤ q)
        (Set.range f) := by
      rintro p ⟨x, rfl⟩ q ⟨y, rfl⟩ hne ⟨⟨t, htne⟩, h1, h2⟩
      obtain ⟨z, hz⟩ := htne
      exact hne (congrArg f ((h1 hz : z = x).symm.trans (h2 hz : z = y)))
    have hcount := (hccc _ hanti).preimage hinj
    rw [Set.preimage_range] at hcount
    exact Cardinal.not_countable_real hcount

-- Logic 14: Martin's Axiom for $\sigma$-centered posets

def MartinAxiom (κ : Cardinal) : Prop :=
    ∀ (P : Type*) [PartialOrder P], IsCCC P →
      ∀ D : Set (Set P), (∀ S ∈ D, IsCoinitial S) → Cardinal.mk D ≤ κ →
      ∀ p : P, ∃ G : Set P, Order.IsPFilter G ∧ p ∈ G ∧ ∀ S ∈ D, (G ∩ S).Nonempty

/-- The principal filter at `p`, the witness used whenever one dense set (or none) has to be
met. -/

theorem isPFilter_Ici {P : Type*} [PartialOrder P] (p : P) : Order.IsPFilter (Set.Ici p) :=
  Order.IsPFilter.of_def ⟨p, Set.self_mem_Ici⟩
    (fun _ hx _ hy => ⟨p, Set.self_mem_Ici, hx, hy⟩) fun hxy hx => le_trans hx hxy

/-- Sanity check: `MartinAxiomSigmaCentered 1` is a theorem of ZFC, so the definition is
satisfiable.

This is a better degenerate case than `κ = 0`, because it actually *uses* `IsCoinitial`: given
one coinitial `S` and a condition `p`, coinitiality supplies `q ∈ S` with `q ≤ p`, and the
principal filter `Set.Ici q` contains `p` and meets `S` at `q`.  Had the definition asked for
`IsCofinal S` instead, the witness `q` would satisfy `p ≤ q` and `p ∈ Set.Ici q` would fail —
so this lemma pins down the direction of the density condition, which the `κ = 0` case cannot.

Note the `IsSigmaCentered` hypothesis is unused here: the statement holds for an arbitrary
poset.  Testing that hypothesis slot is what `MartinAxiom.sigmaCentered` below is for. -/

theorem martinAxiomSigmaCentered_one : MartinAxiomSigmaCentered 1 := by
  intro P _ _ D hD hcard p
  rcases Set.eq_empty_or_nonempty D with rfl | ⟨S, hS⟩
  · exact ⟨Set.Ici p, isPFilter_Ici p, Set.self_mem_Ici, by simp⟩
  · obtain ⟨q, hqS, hqp⟩ := hD S hS p
    refine ⟨Set.Ici q, isPFilter_Ici q, Set.mem_Ici.2 hqp, fun T hT => ?_⟩
    have hTS : T = S := Cardinal.mk_le_one_iff_set_subsingleton.1 hcard hT hS
    exact ⟨q, Set.self_mem_Ici, by rw [hTS]; exact hqS⟩

/-- Sanity check: the axiom gets *weaker* as `κ` grows, i.e. it is antitone.

`κ` bounds how many coinitial sets the filter must meet, so this checks that
`Cardinal.mk D ≤ κ` sits on the hypothesis side with the inequality pointing the right way. -/

theorem _root_.MetaMathlibExt.MartinAxiomSigmaCentered.mono {κ μ : Cardinal} (h : MartinAxiomSigmaCentered κ)
    (hμ : μ ≤ κ) : MartinAxiomSigmaCentered μ := by
  intro P _ hσ D hD hcard p
  exact h P hσ D hD (hcard.trans hμ) p

/-- The `κ = 0` case, now a corollary rather than a separate proof. -/

theorem martinAxiomSigmaCentered_zero : MartinAxiomSigmaCentered 0 :=
  martinAxiomSigmaCentered_one.mono zero_le

/-- Validity, and the check with the most content: full `MartinAxiom κ` implies the
σ-centered fragment.

σ-centered posets are ccc, so restricting the poset hypothesis yields a *weaker* axiom.  This
verifies that `IsSigmaCentered P` occupies the hypothesis slot — the restriction is
contravariant, and the implication would not typecheck if the two axioms differed anywhere
else, or if the restricting predicate had been placed in the conclusion. -/

theorem MartinAxiom.sigmaCentered {κ : Cardinal} (h : MartinAxiom κ) :
    MartinAxiomSigmaCentered κ := by
  intro P _ hσ D hD hcard p
  exact h P hσ.isCCC D hD hcard p

-- Logic 9: Martin's Axiom

/-- Sanity check: `MartinAxiom 0` is a theorem of ZFC, so the definition is satisfiable.

This is the degenerate case of Martin's axiom: `Cardinal.mk D ≤ 0` forces `D = ∅`, and the
principal filter `Set.Ici p` witnesses the conclusion for every `p`.  It is worth stating
because it rules out the definition being accidentally *unsatisfiable* — the shape of the
conclusion (`Order.IsPFilter G ∧ p ∈ G`) really can be met — and because discharging
`Order.IsPFilter` forces the three filter clauses (nonempty, downward directed, upward closed)
to be consistent with `p ∈ G`.

Note this case does not exercise `IsCoinitial`, nor `IsCCC`, nor filter-vs-ideal: the
principal *ideal* `Set.Iic p` would serve equally well.  Those need genuine content
(Rasiowa–Sikorski for `MartinAxiom ℵ₀`, and the failure of `MartinAxiom (2 ^ ℵ₀)`). -/

theorem martinAxiom_zero : MartinAxiom 0 := by
  intro P _ _ D _ hcard p
  refine ⟨Set.Ici p, ?_, Set.self_mem_Ici, ?_⟩
  · exact Order.IsPFilter.of_def ⟨p, Set.self_mem_Ici⟩
      (fun x hx y hy => ⟨p, Set.self_mem_Ici, hx, hy⟩) fun hxy hx => le_trans hx hxy
  · -- `D` is empty, so there is nothing to meet.
    intro S hS
    have : Nonempty D := ⟨⟨S, hS⟩⟩
    exact absurd (le_antisymm hcard zero_le) (Cardinal.mk_ne_zero _)

/-- Sanity check: Martin's axiom gets *weaker* as `κ` grows, i.e. `MartinAxiom` is antitone.

`κ` bounds how many coinitial sets the filter must meet, so a bound of `μ ≤ κ` is a weaker
demand.  This checks that `Cardinal.mk D ≤ κ` sits on the hypothesis side with the inequality
pointing the right way; with `κ ≤ Cardinal.mk D` the proof below would not go through. -/

theorem _root_.MetaMathlibExt.MartinAxiom.mono {κ μ : Cardinal} (h : MartinAxiom κ) (hμ : μ ≤ κ) :
    MartinAxiom μ := by
  intro P _ hccc D hD hcard p
  exact h P hccc D hD (hcard.trans hμ) p

end MathlibExtTest.SetTheory.Forcing.ForcingAxioms.MartinAxiom

end
