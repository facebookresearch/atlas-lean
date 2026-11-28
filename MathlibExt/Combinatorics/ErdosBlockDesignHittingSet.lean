/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.LinearCombination

/-!
# Hitting sets for partial designs

We refute the conjectured uniform bound by trimming the nonvertical lines of a finite affine
plane of prime order `p`. The vertical lines stay intact, so a candidate meeting every block
between one and `C` times is determined by at most `C` entries per column.

Group the columns into `2 * (C + 1)` equal classes, dropping a remainder. On a nonvertical
line we can remove up to `C` classes. If the candidate meets the line in at most `C` points,
remove their classes to miss it entirely. Otherwise leave the line intact. Thus at least one
choice per line defeats each candidate. For large `p`, counting the choices on all `p ^ 2`
lines gives a single family that defeats every candidate.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosBlockDesignHittingSetWanted

/-- **Bounded hitting sets for large partial designs (Erdős Problem 664).** The proposition that
for every real $c$ with $0 < c < 1$ there is a natural number $C$ such that for every natural
number $n$ and every family $\mathcal{B}$ of subsets of $\{0, \dots, n - 1\}$ in which each member
has more than $c\sqrt{n}$ elements and any two distinct members share at most one element, some
set $B \subseteq \{0, \dots, n - 1\}$ meets every member of $\mathcal{B}$ in at least $1$ and at
most $C$ elements. -/
def conjecture : Prop :=
  ∀ c : ℝ, 0 < c → c < 1 →
    ∃ C : ℕ, ∀ n : ℕ, ∀ blocks : Finset (Finset (Fin n)),
      (∀ B ∈ blocks, (B.card : ℝ) > c * Real.sqrt n) →
      (∀ B₁ ∈ blocks, ∀ B₂ ∈ blocks, B₁ ≠ B₂ → (B₁ ∩ B₂).card ≤ 1) →
      ∃ B : Finset (Fin n),
        ∀ A ∈ blocks, 0 < (B ∩ A).card ∧ (B ∩ A).card ≤ C

open Finset

/-- Choose a word agreeing somewhere with each prescribed word. The excluded words for one
prescription have one fewer choice at each coordinate. -/
private theorem exists_agree {A I T : Type*} [Fintype A] [Fintype I] [Fintype T]
    (f : A → I → T)
    (h : Fintype.card A * (Fintype.card T - 1) ^ Fintype.card I <
      Fintype.card T ^ Fintype.card I) :
    ∃ g : I → T, ∀ a, ∃ i, g i = f a i := by
  classical
  let bad (a : A) := Fintype.piFinset fun i => univ.erase (f a i)
  have hcard (a : A) : (bad a).card = (Fintype.card T - 1) ^ Fintype.card I := by
    simp [bad, Fintype.card_piFinset]
  have hlt : (univ.biUnion bad).card < (univ : Finset (I → T)).card := by
    refine (card_biUnion_le.trans ?_).trans_lt (h.trans_eq ?_)
    · simp [hcard]
    · simp
  obtain ⟨g, -, hg⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨g, fun a => ?_⟩
  by_contra! hn
  exact hg (mem_biUnion.mpr ⟨a, mem_univ _, Fintype.mem_piFinset.mpr fun i => by
    simp [hn i]⟩)

/-- For a sufficiently large prime order, the exponential saving on the choices per line
dominates the polynomial number of choices per column. -/
private theorem exists_order (C t lower : ℕ) (ht : 0 < t) :
    ∃ p : ℕ, p.Prime ∧ lower ≤ p ∧ p ^ C * (t - 1) ^ p < t ^ p := by
  have hsub : (t - 1 : ℕ) < t := by omega
  have hratio : |((t - 1 : ℕ) : ℝ) / t| < 1 := by
    rw [abs_of_nonneg (by positivity), div_lt_one (by positivity)]
    exact_mod_cast hsub
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((tendsto_pow_const_mul_const_pow_of_abs_lt_one C hratio).eventually
      (gt_mem_nhds zero_lt_one))
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (max N lower)
  refine ⟨p, hprime, (le_max_right ..).trans hp, ?_⟩
  have h := hN p ((le_max_left ..).trans hp)
  change (p : ℝ) ^ C * (((t - 1 : ℕ) : ℝ) / t) ^ p < 1 at h
  rw [div_pow, ← mul_div_assoc, div_lt_one (by positivity)] at h
  exact_mod_cast h

private def fits {P : Type*} [DecidableEq P] (C : ℕ) (B A : Finset P) : Prop :=
  0 < (B ∩ A).card ∧ (B ∩ A).card ≤ C

/-- Relabel the points so that we can use a product of finite types for the affine plane. -/
private theorem uniform_bound (h : conjecture) :
    ∃ C : ℕ, ∀ (P : Type) [Fintype P] [DecidableEq P] (blocks : Finset (Finset P)),
      (∀ A ∈ blocks, (A.card : ℝ) > (1 / 4 : ℝ) * Real.sqrt (Fintype.card P)) →
      (∀ A ∈ blocks, ∀ D ∈ blocks, A ≠ D → (A ∩ D).card ≤ 1) →
      ∃ B, ∀ A ∈ blocks, fits C B A := by
  classical
  obtain ⟨C, hC⟩ := h (1 / 4) (by norm_num) (by norm_num)
  refine ⟨C, fun P _ _ blocks hsize hpair => ?_⟩
  let e := (Fintype.equivFin P).finsetCongr
  obtain ⟨B, hB⟩ := hC _ (blocks.image e) (by
    simpa [e, Equiv.finsetCongr_apply] using hsize) (by
    simp only [forall_mem_image]
    intro A hA D hD hne
    simpa [e, Equiv.finsetCongr_apply, ← map_inter] using hpair A hA D hD (mt (congrArg e) hne))
  obtain ⟨S, rfl⟩ := e.surjective B
  refine ⟨S, fun A hA => ?_⟩
  simpa [fits, e, Equiv.finsetCongr_apply, ← map_inter] using hB (e A) (mem_image_of_mem e hA)

section Lines

variable {X F : Type*} [Field F]

private def line (e : X ↪ F) (l : F × F) (D : Finset X) : Finset (X × F) :=
  D.map ⟨fun x => (x, l.1 * e x + l.2), fun _ _ h => congrArg Prod.fst h⟩

private theorem mem_line {e : X ↪ F} {l : F × F} {D : Finset X} {z : X × F} :
    z ∈ line e l D ↔ z.1 ∈ D ∧ l.1 * e z.1 + l.2 = z.2 := by
  obtain ⟨x, y⟩ := z
  rw [line, mem_map]
  change (∃ a ∈ D, (a, l.1 * e a + l.2) = (x, y)) ↔ _
  simp [Prod.mk.injEq]

variable [DecidableEq F] [DecidableEq X]

private theorem line_inter_line (e : X ↪ F) {l k : F × F} (hne : l ≠ k) (D E : Finset X) :
    (line e l D ∩ line e k E).card ≤ 1 := by
  classical
  apply card_le_one_iff.mpr
  intro u v hu hv
  obtain ⟨⟨_, hul⟩, ⟨_, huk⟩⟩ := (mem_inter.mp hu).imp mem_line.mp mem_line.mp
  obtain ⟨⟨_, hvl⟩, ⟨_, hvk⟩⟩ := (mem_inter.mp hv).imp mem_line.mp mem_line.mp
  have hmul : (l.1 - k.1) * (e u.1 - e v.1) = 0 := by
    linear_combination hul - huk - hvl + hvk
  rcases mul_eq_zero.mp hmul with hs | hx
  · have hs' := sub_eq_zero.mp hs
    exact (hne (Prod.ext hs' (by rw [hs'] at hul; exact add_left_cancel (hul.trans huk.symm)))).elim
  · have he := e.injective (sub_eq_zero.mp hx)
    exact Prod.ext he (by rw [← hul, ← hvl, he])

variable [Fintype F]

private def column (x : X) : Finset (X × F) := {x} ×ˢ univ

private theorem column_inter_line (x : X) (e : X ↪ F) (l : F × F) (D : Finset X) :
    (column x ∩ line e l D).card ≤ 1 := by
  classical
  apply card_le_one_iff.mpr
  intro u v hu hv
  have hu' : u.1 = x := mem_singleton.mp (mem_product.mp (mem_inter.mp hu).1).1
  have hv' : v.1 = x := mem_singleton.mp (mem_product.mp (mem_inter.mp hv).1).1
  have he := hu'.trans hv'.symm
  exact Prod.ext he (by rw [← (mem_line.mp (mem_inter.mp hu).2).2,
    ← (mem_line.mp (mem_inter.mp hv).2).2, he])

private theorem pairwise_blocks (e : X ↪ F) (D : F × F → Finset X) (i j : X ⊕ (F × F))
    (hne : i ≠ j) :
    ((Sum.elim column (fun l => line e l (D l)) i) ∩
      (Sum.elim column (fun l => line e l (D l)) j)).card ≤ 1 := by
  classical
  cases i with
  | inl x =>
    cases j with
    | inl y =>
      have hxy : x ≠ y := fun h => hne (congrArg Sum.inl h)
      have hempty : (column x ∩ column y : Finset (X × F)) = ∅ := by
        ext z
        simp [column]
        grind
      simp [hempty]
    | inr l => exact column_inter_line x e l (D l)
  | inr l =>
    cases j with
    | inl x => simpa [inter_comm] using column_inter_line x e l (D l)
    | inr k => exact line_inter_line e (fun h => hne (congrArg Sum.inr h)) (D l) (D k)

end Lines

/-- The columns come in equally sized classes. A trimming discards at most `C` classes. -/
private def kept {k : ℕ} (r C : ℕ) (s : Finset (Fin k)) : Finset (Fin k × Fin r) :=
  (if s.card ≤ C then sᶜ else univ) ×ˢ univ

private theorem card_kept {k : ℕ} (r C : ℕ) (s : Finset (Fin k)) :
    (kept r C s).card = (if s.card ≤ C then sᶜ else univ).card * r := by
  rw [kept, card_product, card_univ, Fintype.card_fin]

private theorem exists_bad_trim {k r C : ℕ} {F : Type*} [Field F] [DecidableEq F]
    (e : (Fin k × Fin r) ↪ F) (B : Finset ((Fin k × Fin r) × F)) (l : F × F) :
    ∃ s, ¬ fits C B (line e l (kept r C s)) := by
  classical
  let H := B ∩ line e l univ
  by_cases h : H.card ≤ C
  · let s := H.image fun z => z.1.1
    have hs : s.card ≤ C := card_image_le.trans h
    refine ⟨s, fun hf => ?_⟩
    obtain ⟨z, hz⟩ := card_pos.mp hf.1
    obtain ⟨hzB, hzL⟩ := mem_inter.mp hz
    obtain ⟨hx, hy⟩ := mem_line.mp hzL
    have hzH : z ∈ H := mem_inter.mpr ⟨hzB, mem_line.mpr ⟨mem_univ _, hy⟩⟩
    have hzS : z.1.1 ∈ s := mem_image_of_mem _ hzH
    simp [kept, hs, hzS] at hx
  · refine ⟨∅, fun hf => h ?_⟩
    simpa [kept, H] using hf.2

/-- Enumerate the points in each column, repeating a point if the column has fewer than `C`. -/
private theorem encode_columns {X F : Type*} [DecidableEq X] [DecidableEq F] [Fintype F]
    {C : ℕ} (B : Finset (X × F)) (h : ∀ x, fits C B (column x)) :
    ∃ v : X → Fin C → F, ∀ z, z ∈ B ↔ ∃ i, v z.1 i = z.2 := by
  classical
  let H (x : X) := B ∩ column x
  have (x : X) : Nonempty (H x) := (card_pos.mp (h x).1).to_subtype
  have he (x : X) : Nonempty (H x ↪ Fin C) := Function.Embedding.nonempty_of_card_le
    (by simpa [H] using (h x).2)
  let e (x : X) := (he x).some
  let v (x : X) (i : Fin C) : H x := Function.invFun (e x) i
  refine ⟨fun x i => (v x i).val.2, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · have hzH : z ∈ H z.1 := mem_inter.mpr ⟨hz, by simp [column]⟩
    let u : H z.1 := ⟨z, hzH⟩
    exact ⟨e z.1 u, congrArg (fun w : H z.1 => w.val.2)
      (Function.leftInverse_invFun (e z.1).injective u)⟩
  · rintro ⟨i, hi⟩
    obtain ⟨hu, hx⟩ := mem_inter.mp (v z.1 i).property
    have hx' : (v z.1 i).val.1 = z.1 := mem_singleton.mp (mem_product.mp hx).1
    exact Prod.ext hx' hi ▸ hu

/-- For each enumeration of a candidate set, each line admits a trimming on which it fails.
The counting inequality lets us select just one trimming per line and still defeat them all. -/
private theorem choose_trims {k r C p : ℕ} [Fact p.Prime] (e : (Fin k × Fin r) ↪ ZMod p)
    (hw : k * r ≤ p) (t : ℕ) (ht : t = Fintype.card (Finset (Fin k)))
    (hp : p ^ C * (t - 1) ^ p < t ^ p) :
    ∃ g : ZMod p × ZMod p → Finset (Fin k), ∀ B, (∀ x, fits C B (column x)) →
      ∃ l, ¬ fits C B (line e l (kept r C (g l))) := by
  classical
  let X := Fin k × Fin r
  let F := ZMod p
  let decode (v : X → Fin C → F) : Finset (X × F) := univ.filter fun z => ∃ i, v z.1 i = z.2
  choose bad hbad using fun (v : X → Fin C → F) (l : F × F) =>
    exists_bad_trim (C := C) e (decode v) l
  have hprime : p.Prime := Fact.out
  have hcount : Fintype.card (X → Fin C → F) * (t - 1) ^ Fintype.card (F × F) <
      t ^ Fintype.card (F × F) := by
    simp only [X, F, Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, ZMod.card]
    rw [pow_mul (t - 1), pow_mul t]
    calc
      _ ≤ (p ^ C) ^ p * ((t - 1) ^ p) ^ p :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (pow_pos hprime.pos _) hw)
      _ = (p ^ C * (t - 1) ^ p) ^ p := (mul_pow ..).symm
      _ < _ := Nat.pow_lt_pow_left hp hprime.ne_zero
  obtain ⟨g, hg⟩ := exists_agree bad (ht ▸ hcount)
  refine ⟨g, fun B hB => ?_⟩
  obtain ⟨v, hv⟩ := encode_columns B hB
  have hdecode : B = decode v := by ext z; simp [decode, hv]
  obtain ⟨l, hl⟩ := hg v
  exact ⟨l, hl.symm ▸ hdecode.symm ▸ hbad v l⟩

/--
**Large partial designs need not have uniformly bounded hitting sets.** It is not true that for
every real $c$ with $0 < c < 1$ there is a natural number $C$ such that for every natural number
$n$ and every family $\mathcal{B}$ of subsets of $\{0, \dots, n - 1\}$ in which each member has more
than $c\sqrt{n}$ elements and any two distinct members share at most one element, some set
$B \subseteq \{0, \dots, n - 1\}$ meets every member of $\mathcal{B}$ in at least $1$ and at most
$C$ elements.

Alon answered the question negatively in the source report (Oberwolfach Report 42/2025,
pp. 2249-2250, Theorem 3; also Theorem 2.1 of his note 'Blocking partial designs and
block-compatible sequences'), recorded on erdosproblems.com/664 (DISPROVED): for large prime
powers $q$ and $n = m = q^2 + q + 1$ there is a partial design of $m$ blocks of size
$> 0.4\sqrt{n}$ on $n$ points such that every set meeting all blocks meets some block in at least
$0.1 \log n$ points, so no constant $C$ works for $c \le 0.4$.

Source: N. Alon, On designs and partial designs, extended
abstract in Oberwolfach Report 42/2025 (Combinatorics, Probability and Computing), pp.
2249-2250, Theorem 3, https://doi.org/10.4171/owr/2025/42; N. Alon, Blocking partial designs and
block-compatible sequences, note, Theorem 2.1,
https://web.math.princeton.edu/~nalon/PDFS/remark191.pdf; T. F. Bloom, Erdős Problem #664,
erdosproblems.com (status DISPROVED), https://www.erdosproblems.com/664. Moved from
`OpenConjectures/Combinatorics/ErdosBlockDesignHittingSet`.
-/
public theorem conjecture_refuted : ¬ conjecture := by
  classical
  intro h
  obtain ⟨C, hC⟩ := uniform_bound h
  let k := 2 * (C + 1)
  let t := Fintype.card (Finset (Fin k))
  obtain ⟨p, hprime, hlarge, hp⟩ := exists_order C t (2 * k) Fintype.card_pos
  have : Fact p.Prime := ⟨hprime⟩
  let r := p / k
  let X := Fin k × Fin r
  let F := ZMod p
  have hw : k * r ≤ p := Nat.mul_div_le p k
  obtain ⟨e⟩ : Nonempty (X ↪ F) := Function.Embedding.nonempty_of_card_le
    (by simpa [X, F, ZMod.card] using hw)
  obtain ⟨g, hg⟩ := choose_trims e hw t rfl hp
  let D (l : F × F) := kept r C (g l)
  let block : X ⊕ (F × F) → Finset (X × F) := Sum.elim column fun l => line e l (D l)
  -- The rectangle has at most p² points, and more than p/2 columns.
  have hsqrt : Real.sqrt (Fintype.card (X × F)) ≤ p := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    simp only [X, F, Fintype.card_prod, Fintype.card_fin, ZMod.card, sq]
    exact_mod_cast Nat.mul_le_mul_right p hw
  have hwidth : p < 2 * (k * r) := by
    have hrem := Nat.mod_lt p (show 0 < k by dsimp [k]; omega)
    have hdiv : p % k + k * r = p := Nat.mod_add_div p k
    omega
  have hsize (i) : ((block i).card : ℝ) > (1 / 4 : ℝ) * Real.sqrt (Fintype.card (X × F)) := by
    suffices p < 4 * (block i).card by
      have : (p : ℝ) < 4 * (block i).card := by exact_mod_cast this
      linarith
    cases i with
    | inl x =>
      simp only [block, Sum.elim_inl, column, card_product, card_singleton, card_univ, F,
        ZMod.card, one_mul]
      have := hprime.pos
      omega
    | inr l =>
      have hkeep : k ≤ 2 * (if (g l).card ≤ C then (g l)ᶜ else univ).card := by
        split_ifs with hs
        · simp only [card_compl, Fintype.card_fin]
          dsimp [k]
          omega
        · simp [k]
      calc
        p < 2 * (k * r) := hwidth
        _ ≤ 4 * (block (Sum.inr l)).card := by
          simp only [block, Sum.elim_inr, line, card_map, D]
          change 2 * (k * r) ≤ 4 * (kept r C (g l)).card
          rw [card_kept]
          nlinarith [Nat.mul_le_mul_right r hkeep]
  obtain ⟨B, hB⟩ := hC (X × F) (univ.image block) (by
    simpa only [forall_mem_image, mem_univ, forall_const] using hsize) (by
    simp only [forall_mem_image, mem_univ, forall_const]
    intro i j hne
    exact pairwise_blocks e D i j (mt (congrArg block) hne))
  have hall (i) := hB (block i) (mem_image_of_mem block (mem_univ i))
  obtain ⟨l, hl⟩ := hg B fun x => hall (.inl x)
  exact hl (hall (.inr l))

end MathlibExt.Combinatorics.ErdosBlockDesignHittingSetWanted
