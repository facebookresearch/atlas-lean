/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Basic.Denumerable
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Rat.Denumerable
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ZMod.Basic
public import MathlibExt.GroupTheory.CompleteLatticeOfFormationsKourovka18Problem92

/-!
# Non-algebraic complete lattices of formations (Kourovka Notebook Problem 18.92(a))

Kourovka Notebook, Problem 18.92 (A. N. Skiba), marked solved in the 21st issue: a non-empty set `θ`
of formations is a complete lattice of formations if the intersection of any set of formations in
`θ` belongs to `θ` and `θ` has a largest element. An element `a` of a complete lattice is compact if
`a ≤ ⋁X` implies `a ≤ ⋁X₁` for a finite `X₁ ⊆ X`, and the lattice is algebraic if every element is a
join of compact elements. (a) Is there a non-algebraic complete lattice of formations of finite
groups? (b) Is there a non-modular complete lattice of formations of finite groups?

The main result is `nonAlgebraicCompleteLatticeOfFormations_holds`: there is a complete lattice of
formations of finite groups that is not algebraic. The proof uses a dense chain of
prime-support classes indexed by the reals in `[0, 1]`, so that only the bottom element of the
chain is compact.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.92 (A. N. Skiba). UnsolvedMath record
UM-00701521 (`KOU-18.92`), dataset ulamai/UnsolvedMath v1.8.0.

Classes of groups are isomorphism-closed predicates on groups in `Type` (`GroupClass`, as in the
WantedExt module for Kourovka 12.97); a formation consists of finite groups, contains the trivial
group, and is closed under quotients and finite subdirect products (`G ⧸ N₁, G ⧸ N₂ ∈ X → G ⧸ (N₁ ⊓
N₂) ∈ X`). Intersections of nonempty subsets of `θ` lie in `θ` (the empty intersection is replaced
by the largest element). Order is inclusion; joins are least upper bounds inside `θ` and meets are
intersections, as in the problem's definition. The resolution is an AI-generated solution confirmed
by A. N. Skiba.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.CompleteLatticeOfFormationsKourovka18Problem92Wanted

/-- A bijection between the primes and the rationals, used to index a dense chain of
prime-support classes by the reals. -/
private noncomputable def primeRatEquiv : ↥{p | Nat.Prime p} ≃ ℚ := by
  haveI : Infinite ↥{p | Nat.Prime p} := Nat.infinite_setOfPred_prime.to_subtype
  letI := Nat.Subtype.denumerable {p | Nat.Prime p}
  exact Denumerable.equiv₂ _ _

/-- The rational label assigned to a prime by `primeRatEquiv`. -/
private noncomputable def primeLabel (p : ℕ) (hp : p.Prime) : ℚ := primeRatEquiv ⟨p, hp⟩

private theorem primeLabel_irrel (p : ℕ) (hp hp' : p.Prime) :
    primeLabel p hp = primeLabel p hp' :=
  rfl

/-- The prime whose label is `q`. -/
private noncomputable def primeOfRat (q : ℚ) : ℕ := (primeRatEquiv.symm q).1

private theorem primeOfRat_prime (q : ℚ) : (primeOfRat q).Prime :=
  (primeRatEquiv.symm q).2

private theorem primeLabel_primeOfRat (q : ℚ) :
    primeLabel (primeOfRat q) (primeOfRat_prime q) = q := by
  change primeRatEquiv (primeRatEquiv.symm q) = q
  exact Equiv.apply_symm_apply _ _

/-- The set of primes whose rational label is at most `t`. -/
private def cutSet (t : ℝ) : Set ℕ :=
  {p | ∃ hp : p.Prime, (primeLabel p hp : ℝ) ≤ t}

private theorem cutSet_mono {s t : ℝ} (h : s ≤ t) : cutSet s ⊆ cutSet t := by
  rintro p ⟨hp, hle⟩
  exact ⟨hp, hle.trans h⟩

private theorem prime_mem_cutSet {t : ℝ} {p : ℕ} (hp : p.Prime)
    (hle : (primeLabel p hp : ℝ) ≤ t) : p ∈ cutSet t :=
  ⟨hp, hle⟩

/-- Every prime whose label is at most `t` lies in the cut at `t`, and labels separate
cuts: if `s < t` some prime lies in the cut at `t` but not in the cut at `s`. -/
private theorem exists_prime_in_cutSet_diff {s t : ℝ} (h : s < t) :
    ∃ p, p ∈ cutSet t ∧ p ∉ cutSet s := by
  obtain ⟨q, hs, ht⟩ := exists_rat_btwn h
  refine ⟨primeOfRat q, prime_mem_cutSet (primeOfRat_prime q) ?_, ?_⟩
  · rw [primeLabel_primeOfRat]
    exact ht.le
  · rintro ⟨hp, hle⟩
    rw [primeLabel_irrel _ hp (primeOfRat_prime q),
      primeLabel_primeOfRat] at hle
    exact absurd (hle.trans_lt hs) (lt_irrefl _)

/-- The dense chain of prime-support formations indexed by `[0, 1]`. -/
private def chainTheta : Set GroupClass :=
  Set.range fun t : Set.Icc (0 : ℝ) 1 => primeSupportClass (cutSet t.1)

private theorem mem_chainTheta {X : GroupClass} :
    X ∈ chainTheta ↔ ∃ t : Set.Icc (0 : ℝ) 1, X = primeSupportClass (cutSet t.1) := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl⟩

private theorem primeSupportClass_mono' {S T : Set ℕ} (h : S ⊆ T) :
    Incl (primeSupportClass S) (primeSupportClass T) :=
  fun _ _ hG ↦ ⟨hG.1, fun p hp hd ↦ h (hG.2 p hp hd)⟩

private theorem incl_trans {X Y Z : GroupClass} (h₁ : Incl X Y) (h₂ : Incl Y Z) :
    Incl X Z :=
  fun _ _ h ↦ h₂ _ (h₁ _ h)

private theorem prime_mem_of_incl' {S T : Set ℕ}
    (h : Incl (primeSupportClass S) (primeSupportClass T)) {p : ℕ} (hp : p.Prime)
    (hS : p ∈ S) : p ∈ T := by
  have : NeZero p := ⟨hp.ne_zero⟩
  let G := Multiplicative (ZMod p)
  have hcard : Nat.card G = p := Nat.card_zmod p
  have hG : (primeSupportClass S).mem G := by
    refine ⟨inferInstance, fun q hq hd ↦ ?_⟩
    rwa [(Nat.prime_dvd_prime_iff_eq hq hp).mp (hcard ▸ hd)]
  exact (h G hG).2 p hp (hcard ▸ dvd_rfl)

/-- The chain is closed under nonempty intersections: the intersection is the cut at the
infimum of the indices. -/
private theorem chainTheta_complete : IsCompleteLatticeOfFormations chainTheta := by
  refine ⟨⟨_, mem_chainTheta.mpr ⟨⟨0, by norm_num⟩, rfl⟩⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact isFormation_primeSupportClass _
  · intro D hD hne
    let T : Set ℝ := {r | ∃ X ∈ D, ∃ t : Set.Icc (0 : ℝ) 1, t.1 = r ∧
      X = primeSupportClass (cutSet t.1)}
    have hTne : T.Nonempty := by
      obtain ⟨X, hX⟩ := hne
      obtain ⟨t, ht⟩ := mem_chainTheta.mp (hD hX)
      exact ⟨t.1, X, hX, t, rfl, ht⟩
    have hTbdd : BddBelow T := by
      refine ⟨0, fun r hr ↦ ?_⟩
      obtain ⟨-, -, t, rfl, -⟩ := hr
      exact t.2.1
    have hle1 : sInf T ≤ 1 := by
      obtain ⟨r, hr⟩ := hTne
      have hr' := hr
      obtain ⟨-, -, t, htr, -⟩ := hr
      calc sInf T ≤ r := csInf_le hTbdd hr'
        _ = t.1 := htr.symm
        _ ≤ 1 := t.2.2
    refine ⟨primeSupportClass (cutSet (sInf T)),
      mem_chainTheta.mpr ⟨⟨sInf T, le_csInf hTne (fun r hr ↦ by
        obtain ⟨-, -, t, rfl, -⟩ := hr
        exact t.2.1), hle1⟩, rfl⟩, ?_⟩
    intro G _
    constructor
    · intro h X hX
      obtain ⟨t, ht⟩ := mem_chainTheta.mp (hD hX)
      rw [ht]
      refine ⟨h.1, fun p hp hd ↦ ?_⟩
      obtain ⟨hp', hle⟩ := h.2 p hp hd
      refine ⟨hp, ?_⟩
      rw [primeLabel_irrel _ hp' hp] at hle
      exact hle.trans (csInf_le hTbdd ⟨X, hX, t, rfl, ht⟩)
    · intro h
      obtain ⟨X, hX⟩ := hne
      obtain ⟨t, ht⟩ := mem_chainTheta.mp (hD hX)
      have hmem := h X hX
      rw [ht] at hmem
      refine ⟨hmem.1, fun p hp hd ↦ ?_⟩
      have hle : (primeLabel p hp : ℝ) ≤ sInf T := by
        refine le_csInf hTne fun r hr ↦ ?_
        obtain ⟨Y, hY, u, rfl, hu⟩ := hr
        have hYmem := h Y hY
        rw [hu] at hYmem
        obtain ⟨hp', hle⟩ := hYmem.2 p hp hd
        rw [primeLabel_irrel _ hp' hp] at hle
        exact hle
      exact ⟨hp, hle⟩
  · refine ⟨_, mem_chainTheta.mpr ⟨⟨1, by norm_num⟩, rfl⟩, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact primeSupportClass_mono' (cutSet_mono t.2.2)

/-- The classes strictly below `u` in the chain. -/
private def predSet (u : ℝ) : Set GroupClass :=
  Set.range fun s : Set.Ico (0 : ℝ) u => primeSupportClass (cutSet s.1)

/-- The join of the strict predecessors of a positive element is that element. -/
private theorem isJoinIn_preds {u : Set.Icc (0 : ℝ) 1} (hu : 0 < u.1) :
    IsJoinIn chainTheta (predSet u.1) (primeSupportClass (cutSet u.1)) := by
  refine ⟨mem_chainTheta.mpr ⟨u, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    exact primeSupportClass_mono' (cutSet_mono s.2.2.le)
  · intro U hU hle
    obtain ⟨v, rfl⟩ := mem_chainTheta.mp hU
    apply primeSupportClass_mono'
    intro p hp
    by_contra hnot
    have hvu : v.1 < u.1 := by
      by_contra hcon
      push Not at hcon
      exact absurd (cutSet_mono hcon hp) hnot
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hvu
    have hq0 : (0 : ℝ) ≤ q := le_trans v.2.1 hq1.le
    have hs0 : 0 ≤ (↑q + u.1) / 2 := by positivity
    have hsu : (↑q + u.1) / 2 < u.1 := by linarith
    have hqs : (q : ℝ) ≤ (↑q + u.1) / 2 := by linarith
    have hmem : primeOfRat q ∈ cutSet ((↑q + u.1) / 2) :=
      prime_mem_cutSet (primeOfRat_prime q) (by rw [primeLabel_primeOfRat]; exact hqs)
    have hle' := hle _ ⟨⟨(↑q + u.1) / 2, hs0, hsu⟩, rfl⟩
    have := prime_mem_of_incl' hle' (primeOfRat_prime q) hmem
    obtain ⟨hp, hle''⟩ := this
    rw [primeLabel_irrel _ hp (primeOfRat_prime q), primeLabel_primeOfRat] at hle''
    exact absurd (hle''.trans_lt hq1) (lt_irrefl _)

/-- A finite set of strict predecessors is covered by one strict predecessor. -/
private theorem exists_cover {u : ℝ} (hu : 0 < u) {P₁ : Set GroupClass}
    (hfin : P₁.Finite) (hsub : P₁ ⊆ predSet u) :
    ∃ s, s < u ∧ 0 ≤ s ∧ ∀ X ∈ P₁, Incl X (primeSupportClass (cutSet s)) := by
  revert hsub
  refine @Set.Finite.induction_on _
    (fun S _ => S ⊆ predSet u →
      ∃ s, s < u ∧ 0 ≤ s ∧ ∀ X ∈ S, Incl X (primeSupportClass (cutSet s)))
    P₁ hfin ?_ ?_
  · intro _
    exact ⟨0, hu, le_refl 0, fun X hX ↦ absurd hX (Set.notMem_empty X)⟩
  · intro a s ha hs ih hsub
    obtain ⟨s₀, hsu, hs0, hcover⟩ :=
      ih (fun X hX ↦ hsub (Set.mem_insert_of_mem _ hX))
    obtain ⟨b, rfl⟩ := hsub (Set.mem_insert _ _)
    refine ⟨max s₀ b.1, max_lt hsu b.2.2, le_max_of_le_left hs0, ?_⟩
    intro X hX
    rcases Set.mem_insert_iff.mp hX with rfl | hX
    · exact primeSupportClass_mono' (cutSet_mono (le_max_right _ _))
    · exact incl_trans (hcover X hX)
        (primeSupportClass_mono' (cutSet_mono (le_max_left _ _)))

/-- No positive element of the chain is compact. -/
private theorem not_compact {u : Set.Icc (0 : ℝ) 1} (hu : 0 < u.1) :
    ¬ IsCompactIn chainTheta (primeSupportClass (cutSet u.1)) := by
  intro hcomp
  obtain ⟨P₁, hsub, hfin, J₁, hjoin, hle⟩ :=
    hcomp (predSet u.1) (fun X hX ↦ by
      obtain ⟨s, rfl⟩ := hX
      exact mem_chainTheta.mpr ⟨⟨s.1, s.2.1, s.2.2.le.trans u.2.2⟩, rfl⟩)
      _ (isJoinIn_preds hu) (fun _ _ h ↦ h)
  obtain ⟨s, hsu, hs0, hcover⟩ := exists_cover hu hfin hsub
  have hleJ : Incl J₁ (primeSupportClass (cutSet s)) :=
    hjoin.2.2 _ (mem_chainTheta.mpr ⟨⟨s, hs0, hsu.le.trans u.2.2⟩, rfl⟩) hcover
  have hle' : Incl (primeSupportClass (cutSet u.1)) (primeSupportClass (cutSet s)) :=
    incl_trans hle hleJ
  obtain ⟨p, hpU, hpS⟩ := exists_prime_in_cutSet_diff hsu
  exact hpS (prime_mem_of_incl' hle' (by
    obtain ⟨hp, -⟩ := hpU
    exact hp) hpU)

/-- **Non-algebraic complete lattices of formations exist.** There is a set $\Theta$ of classes of
groups that is a complete lattice of formations of finite groups and is not algebraic; that is,
Kourovka Problem 18.92(a) has a positive answer.

The Kourovka Notebook (21st issue) answers 18.92(a) "Yes", by an AI-generated solution confirmed by
A. N. Skiba (Kinyon–Urban, 2026): for a set $S$ of primes let $\mathfrak{F}_S$ be the class of
finite groups whose order has all its prime divisors in $S$; the classes $\mathfrak{F}_S$ with $S$
finite, together with the class of all finite groups, form a complete lattice of formations whose
only compact element is the bottom.

Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Problem 18.92 (A. N. Skiba); resolution: M. Kinyon and J.
Urban, Results on problems from the Kourovka Notebook, preprint, version 4, 19 September 2026,
Section 3.29 (Problem 18.92): with F_S the finite groups whose order has all prime divisors in S,
{F_S : S finite} ∪ {F_P} is not algebraic and the formations with prime sets ∅, {2}, {2, 3}, {5}, P
form a pentagon N_5; an AI solution confirmed by A. N. Skiba, accepted in the Kourovka Notebook
(21st issue),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka-mathematics.pdf.
-/
public theorem nonAlgebraicCompleteLatticeOfFormations_holds :
    nonAlgebraicCompleteLatticeOfFormations := by
  refine ⟨chainTheta, chainTheta_complete, ?_⟩
  intro halg
  obtain ⟨S, hSΘ, hcomp, hjoin⟩ :=
    halg _ (mem_chainTheta.mpr ⟨⟨1, by norm_num⟩, rfl⟩)
  have hbot : ∀ X ∈ S, X = primeSupportClass (cutSet 0) := by
    intro X hX
    obtain ⟨v, rfl⟩ := mem_chainTheta.mp (hSΘ hX)
    by_contra hne
    have hv0 : v.1 ≠ 0 := fun hv0 ↦ hne (by rw [hv0])
    have hv : 0 < v.1 := lt_of_le_of_ne v.2.1 (Ne.symm hv0)
    exact not_compact hv (hcomp _ hX)
  have hle : Incl (primeSupportClass (cutSet 1)) (primeSupportClass (cutSet 0)) :=
    hjoin.2.2 _ (mem_chainTheta.mpr ⟨⟨0, by norm_num⟩, rfl⟩)
      (fun X hX ↦ by rw [hbot X hX]; exact fun _ _ h ↦ h)
  obtain ⟨p, hp1, hp0⟩ := exists_prime_in_cutSet_diff (show (0 : ℝ) < 1 by norm_num)
  exact hp0 (prime_mem_of_incl' hle (by obtain ⟨hp, -⟩ := hp1; exact hp) hp1)

end MathlibExt.GroupTheory.CompleteLatticeOfFormationsKourovka18Problem92Wanted
