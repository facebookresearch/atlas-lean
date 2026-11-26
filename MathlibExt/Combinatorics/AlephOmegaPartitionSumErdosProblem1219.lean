/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.SetTheory.Cardinal.Pigeonhole

/-!
# A partition relation for sums of increasing powers of two (Erdős Problem 1219)

This file proves Shelah's partition relation for Erdős Problem 1219.

Erdős Problem 1219: let `(nₖ)` be an increasing sequence of integers such that `2^{ℵ_{nₖ}}` is
strictly increasing and `2^{ℵ_{n₀}} > ℵ_ω`. Then `∑ₖ 2^{ℵ_{nₖ}} → (ℵ_ω)²`.

In the absence of an `ℵ_ω`-sized homogeneous set, an asymmetric partition bound produces
large sets in both colours. We choose these sets in countably many blocks, with a constant
cross-colour between blocks, and use the infinite Ramsey theorem on the block indices.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.AlephOmegaPartitionSumErdosProblem1219Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1219, https://www.erdosproblems.com/1219 (status
PROVED). UnsolvedMath record UM-30007260 (`EP-1219`), dataset ulamai/UnsolvedMath v1.8.0.

The arrow is the Erdős-Rado partition relation for pairs with two colours: every symmetric
two-colouring of the pairs of a set of cardinality `∑ₖ 2^{ℵ_{nₖ}}` (a cardinal sum) has a
homogeneous set of cardinality `ℵ_ω`. Cardinals are in `Cardinal.{0}`. Compared with the
formal-conjectures statement `ErdosProblems/1219.lean` (equivalent; no code imported).
-/

open Cardinal

/-- **Partition relation for pairs with two colours.** For cardinals $\kappa$ and $\mu$, the
relation $\kappa \to (\mu)^2_2$ holds if for every set $X$ of cardinality $\kappa$ and every
symmetric colouring $c$ of the ordered pairs of elements of $X$ with two colours, there are a
subset $H \subseteq X$ of cardinality $\mu$ and a colour $b$ such that $c(x, y) = b$ for all
distinct $x, y \in H$. -/
def ArrowsPairs (κ μ : Cardinal.{0}) : Prop :=
  ∀ (α : Type), #α = κ → ∀ c : α → α → Bool, (∀ x y, c x y = c y x) →
    ∃ H : Set α, #H = μ ∧ ∃ b : Bool, ∀ x ∈ H, ∀ y ∈ H, x ≠ y → c x y = b

/-- **Erdős Problem 1219: a partition relation for sums of powers of two.** The statement that for
every strictly increasing sequence $n_0 < n_1 < \cdots$ of natural numbers such that the cardinals
$2^{\aleph_{n_k}}$ are strictly increasing in $k$ and $2^{\aleph_{n_0}} > \aleph_\omega$, the
partition relation $\sum_k 2^{\aleph_{n_k}} \to (\aleph_\omega)^2_2$ holds: for every set $X$ of
cardinality $\sum_k 2^{\aleph_{n_k}}$ and every symmetric colouring of the pairs of elements of $X$
with two colours, some subset of $X$ of cardinality $\aleph_\omega$ has all pairs of distinct
elements of the same colour. -/
def alephOmegaPartitionOfCardinalSum : Prop :=
  ∀ n : ℕ → ℕ, StrictMono n → StrictMono (fun k => (2 : Cardinal.{0}) ^ ℵ_ (n k)) →
    ℵ_ Ordinal.omega0 < (2 : Cardinal.{0}) ^ ℵ_ (n 0) →
      ArrowsPairs (Cardinal.sum fun k : ℕ => (2 : Cardinal.{0}) ^ ℵ_ (n k)) (ℵ_ Ordinal.omega0)

open Function Order Set

private def Monochromatic {α : Type} (c : α → α → Bool) (b : Bool) (s : Set α) : Prop :=
  s.Pairwise fun x y => c x y = b

private theorem smallSet_code {α θ : Type} (s : Set α) (hs : #s ≤ #θ) :
    ∃ f : θ → Option α, ∀ x : α, x ∈ s ↔ some x ∈ range f := by
  classical
  obtain ⟨e⟩ := (Cardinal.le_def _ _).mp hs
  let g : θ → Option α := Function.extend e (fun x : s => some x.val) (fun _ => none)
  have he (x : s) : g (e x) = some x.val := e.injective.extend_apply _ _ x
  refine ⟨g, fun x => ⟨fun hx => ⟨e ⟨x, hx⟩, he ⟨x, hx⟩⟩, ?_⟩⟩
  rintro ⟨t, ht⟩
  by_cases hm : t ∈ range e
  · obtain ⟨y, rfl⟩ := hm
    rw [he, Option.some.injEq] at ht
    exact ht ▸ y.property
  · have hn : g t = none := extend_apply' _ _ _ hm
    rw [hn] at ht
    cases ht

private theorem option_power_le {α θ : Type} {κ : Cardinal}
    (hκ : ℵ₀ ≤ κ) (hα : #α ≤ 2 ^ κ) (hθ : #θ = κ) :
    #(θ → Option α) ≤ 2 ^ κ := by
  rw [mk_arrow, hθ, mk_option, lift_id, lift_id]
  have htwo : ℵ₀ ≤ (2 : Cardinal) ^ κ := hκ.trans (cantor κ).le
  calc
    (#α + 1) ^ κ ≤ ((2 : Cardinal) ^ κ) ^ κ := by
      apply power_le_power_right
      exact (add_le_max _ _).trans
        (max_le (max_le hα (one_le_aleph0.trans htwo)) htwo)
    _ = 2 ^ κ := by rw [← power_mul, mul_eq_self hκ]

private theorem mk_smallSets_le {α : Type} {κ : Cardinal}
    (hκ : ℵ₀ ≤ κ) (hα : #α ≤ 2 ^ κ) :
    #{s : Set α // #s ≤ κ} ≤ 2 ^ κ := by
  let code : (κ.out → Option α) → {s : Set α // #s ≤ κ} :=
    fun f => ⟨{x | some x ∈ range f},
      (mk_le_of_injective (f := fun x => (⟨some x.val, x.property⟩ : range f))
        (fun _ _ h => Subtype.ext (Option.some.inj (congrArg Subtype.val h)))).trans
          (mk_range_le.trans_eq (mk_out _))⟩
  apply (mk_le_of_surjective (f := code) ?_).trans (option_power_le hκ hα (mk_out _))
  intro s
  obtain ⟨f, hf⟩ := smallSet_code s.val (s.property.trans_eq (mk_out _).symm)
  exact ⟨f, Subtype.ext (Set.ext fun x => (hf x).symm)⟩

-- Follow the colour pattern of x, choosing each pivot from the points that
-- agree with x on all previous pivots. A fixed choice function makes the
-- pivots depend only on the pattern seen so far.
private noncomputable def pivot {α ι : Type} [LT ι] [WellFoundedLT ι]
    (pick : Set α → α) (c : α → α → Bool) (x : α) : ι → α :=
  wellFounded_lt.fix fun i prev =>
    pick {y | ∀ j (hj : j < i), y ≠ prev j hj ∧ c (prev j hj) y = c (prev j hj) x}

private theorem pivot_eq {α ι : Type} [LT ι] [WellFoundedLT ι]
    (pick : Set α → α) (c : α → α → Bool) (x : α) (i : ι) :
    pivot pick c x i =
      pick {y | ∀ j < i, y ≠ pivot pick c x j ∧ c (pivot pick c x j) y = c (pivot pick c x j) x} :=
  wellFounded_lt.fix_eq _ i

-- If b has no large homogeneous set, the positions marked b on each
-- branch are few. Those positions and the first pivot equal to x encode x.
private theorem exists_large_monochromatic {α : Type} {κ δ : Cardinal}
    (hκ : ℵ₀ ≤ κ) (hκδ : κ ≤ δ) (hδ : δ ≤ 2 ^ κ) (hα : 2 ^ κ < #α)
    (c : α → α → Bool) (hc : ∀ x y, c x y = c y x) (b : Bool) :
    (∃ s : Set α, δ ≤ #s ∧ Monochromatic c (!b) s) ∨
      ∃ s : Set α, κ ≤ #s ∧ Monochromatic c b s := by
  classical
  by_contra! h
  have hbad (s : Set α) (hs : Monochromatic c b s) : #s < κ := lt_of_not_ge fun he => h.2 s he hs
  have hother (s : Set α) (hs : Monochromatic c (!b) s) : #s < δ :=
    lt_of_not_ge fun he => h.1 s he hs
  have hnonempty : Nonempty α := mk_ne_zero_iff.mp (ne_of_gt (zero_le.trans_lt hα))
  let pick (s : Set α) : α := if hs : s.Nonempty then hs.choose else hnonempty.some
  have hpick (s : Set α) (hs : s.Nonempty) : pick s ∈ s := by
    simpa only [pick, dite_eq_left hs] using hs.choose_spec
  let ι : Type := δ.ord.ToType
  have hι : #ι = δ := by simp [ι]
  let p : α → ι → α := pivot pick c
  have hstep (x : α) (i : ι) (hi : ∀ j < i, p x j ≠ x) :
      ∀ j < i, p x i ≠ p x j ∧ c (p x j) (p x i) = c (p x j) x := by
    change ∀ j < i, pivot pick c x i ≠ p x j ∧ c (p x j) (pivot pick c x i) = c (p x j) x
    rw [pivot_eq]
    let candidates : Set α :=
      {y | ∀ j < i, y ≠ p x j ∧ c (p x j) y = c (p x j) x}
    exact hpick candidates ⟨x, fun j hj => ⟨(hi j hj).symm, rfl⟩⟩
  have hmono (x : α) (s : Set ι) (d : Bool)
      (hbefore : ∀ i ∈ s, ∀ j < i, p x j ≠ x)
      (hcolor : ∀ i ∈ s, c (p x i) x = d) :
      #(p x '' s) = #s ∧ Monochromatic c d (p x '' s) := by
    have hs (i) (hi : i ∈ s) (j) (hj : j ∈ s) (hij : i < j) :
        p x j ≠ p x i ∧ c (p x i) (p x j) = d := by
      have hh := hstep x j (hbefore j hj) i hij
      exact ⟨hh.1, hh.2.trans (hcolor i hi)⟩
    refine ⟨mk_image_eq_of_injOn _ _ ?_, ?_⟩
    · intro i hi j hj he
      rcases lt_trichotomy i j with hij | rfl | hji
      · exact False.elim ((hs i hi j hj hij).1 he.symm)
      · rfl
      · exact False.elim ((hs j hj i hi hji).1 he)
    · rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ hne
      rcases lt_trichotomy i j with hij | rfl | hji
      · exact (hs i hi j hj hij).2
      · exact (hne rfl).elim
      · exact (hc _ _).trans (hs j hj i hi hji).2
  have hhit (x : α) : ∃ i, p x i = x := by
    by_contra! hx
    let s (d : Bool) : Set ι := {i | c (p x i) x = d}
    have hs (d) := hmono x (s d) d (fun _ _ j _ => hx j) (fun _ hi => hi)
    have hb : #(s b) < κ := by rw [← (hs b).1]; exact hbad _ (hs b).2
    have hnb : #(s (!b)) < δ := by rw [← (hs (!b)).1]; exact hother _ (hs (!b)).2
    have hunion : s b ∪ s (!b) = Set.univ := by
      ext i
      cases b <;> cases c (p x i) x <;> simp [s, *]
    have hlt := (mk_union_le (s b) (s (!b))).trans_lt
      (add_lt_of_lt (hκ.trans hκδ) (hb.trans_le hκδ) hnb)
    rw [hunion, mk_univ, hι] at hlt
    exact hlt.false
  let first (x : α) : ι :=
    wellFounded_lt.min {i | p x i = x} (hhit x)
  have hfirst (x) : p x (first x) = x :=
    wellFounded_lt.min_mem {i | p x i = x} (hhit x)
  have hbefore (x) (j) (hj : j < first x) : p x j ≠ x :=
    fun he => wellFounded_lt.not_lt_min {i | p x i = x} he hj
  let mark (x : α) : Set ι := {i | i < first x ∧ c (p x i) x = b}
  have hmark (x : α) : #(mark x) ≤ κ := by
    obtain ⟨he, hm⟩ := hmono x (mark x) b
      (fun _ hi j hj => hbefore x j (hj.trans hi.1)) (fun _ hi => hi.2)
    rw [← he]
    exact (hbad _ hm).le
  let code (x : α) : ι × {s : Set ι // #s ≤ κ} := ⟨first x, mark x, hmark x⟩
  have hinj : Injective code := by
    intro x y hxy
    have hindex : first x = first y := congrArg Prod.fst hxy
    have hmarks : mark x = mark y := congrArg (fun a => a.2.val) hxy
    suffices ∀ i ≤ first x, p x i = p y i by
      rw [← hfirst x, ← hfirst y, ← hindex, this _ le_rfl]
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      intro hi
      change pivot pick c x i = pivot pick c y i
      rw [pivot_eq, pivot_eq]
      congr 1
      ext z
      change (∀ j < i, z ≠ p x j ∧ c (p x j) z = c (p x j) x) ↔
        (∀ j < i, z ≠ p y j ∧ c (p y j) z = c (p y j) y)
      have hcolor (j) (hj : j < i) : c (p x j) x = c (p y j) y := by
        have hjx := hj.trans_le hi
        have hjy := hindex ▸ hjx
        have hm : j ∈ mark x ↔ j ∈ mark y := by rw [hmarks]
        change (_ ∧ c (p x j) x = b) ↔ (_ ∧ c (p y j) y = b) at hm
        rw [and_iff_right hjx, and_iff_right hjy] at hm
        revert hm
        generalize c (p x j) x = a
        generalize c (p y j) y = d
        cases a <;> cases d <;> cases b <;> simp
      exact forall₂_congr fun j hj => by rw [hcolor j hj, ih j hj (hj.le.trans hi)]
  apply hα.not_ge
  refine (mk_le_of_injective hinj).trans ?_
  rw [mk_prod, lift_id, lift_id]
  exact (mul_le_mul' (hι.trans_le hδ) (mk_smallSets_le hκ (hι.trans_le hδ))).trans_eq
    (mul_eq_self (hκ.trans (cantor κ).le))


-- There are at most 2^κ colour patterns on subsets of size at most κ of S.
-- Delete the small fibres of all these patterns to find a representative y
-- whose colour pattern on every such subset has a full-sized fibre.
private theorem exists_representative {α : Type} {κ : Cardinal} {S A : Set α}
    (hκ : ℵ₀ ≤ κ) (hS : #S ≤ 2 ^ κ) (hA : #A = succ (2 ^ κ))
    (c : α → α → Bool) :
    ∃ y ∈ A, ∀ T : Set α, T ⊆ S → #T ≤ κ →
      succ (2 ^ κ) ≤ #{x ∈ A | ∀ z ∈ T, c z x = c z y} := by
  classical
  let ι := (κ.out → Option S) × (κ.out → Bool)
  let pattern (f : κ.out → Option S) (x : α) (i : κ.out) : Bool :=
    (f i).elim false (fun z => c z.val x)
  let fiber (q : ι) : Set α := {x ∈ A | pattern q.1 x = q.2}
  let bad (q : ι) : Set α := if #(fiber q) < succ (2 ^ κ) then fiber q else ∅
  have hκ' : ℵ₀ ≤ (2 : Cardinal) ^ κ := hκ.trans (cantor κ).le
  have hι : #ι ≤ 2 ^ κ := by
    change #((κ.out → Option S) × (κ.out → Bool)) ≤ 2 ^ κ
    rw [mk_prod, lift_id, lift_id]
    have hbool : #(κ.out → Bool) = 2 ^ κ := by rw [mk_arrow, mk_out, mk_bool, lift_id, lift_id]
    rw [hbool]
    exact (mul_le_mul' (option_power_le hκ hS (mk_out _)) le_rfl).trans_eq
      (mul_eq_self hκ')
  have hbad : #(⋃ q, bad q) < succ (2 ^ κ) := by
    apply (card_iUnion_lt_iff_forall_of_isRegular (isRegular_succ hκ')
      (hι.trans_lt (lt_succ _))).mpr
    intro q
    by_cases h : #(fiber q) < succ (2 ^ κ)
    · simpa only [bad, ite_eq_left h]
    · have he : bad q = ∅ := ite_eq_right h
      change #(bad q) < _
      rw [he, mk_eq_zero_iff.mpr (inferInstance : IsEmpty (∅ : Set α))]
      exact zero_le.trans_lt (lt_succ _)
  have hex : (A \ ⋃ q, bad q).Nonempty := by
    by_contra! h
    have hsub : A ⊆ ⋃ q, bad q := by simpa [sdiff_eq_empty] using h
    exact hbad.not_ge (hA ▸ mk_le_mk_of_subset hsub)
  obtain ⟨y, hy, hnotbad⟩ := hex
  refine ⟨y, hy, fun T hTS hT => ?_⟩
  have hpre : #(Subtype.val ⁻¹' T : Set S) ≤ #κ.out := by
    rw [mk_out, mk_preimage_of_injective_of_subset_range _ _ Subtype.val_injective]
    · exact hT
    · simpa using hTS
  obtain ⟨f, hf⟩ := smallSet_code (Subtype.val ⁻¹' T : Set S) hpre
  let q : ι := (f, pattern f y)
  have hlarge : succ (2 ^ κ) ≤ #(fiber q) := by
    by_contra! h
    apply hnotbad
    apply mem_iUnion.mpr
    exact ⟨q, by simpa only [bad, ite_eq_left h] using (show y ∈ fiber q from ⟨hy, rfl⟩)⟩
  apply hlarge.trans (mk_le_mk_of_subset ?_)
  rintro x ⟨hx, hcolor⟩
  refine ⟨hx, fun z hz => ?_⟩
  obtain ⟨i, hi⟩ := (hf ⟨z, hTS hz⟩).mp hz
  simpa only [q, pattern, hi, Option.elim_some] using congrFun hcolor i

open Filter in
private theorem exists_monochromatic_indices (c : ℕ → ℕ → Bool) :
    ∃ (v : ℕ → ℕ) (b : Bool), StrictMono v ∧ ∀ i j, i < j → c (v i) (v j) = b := by
  classical
  obtain ⟨U, hU⟩ := Filter.exists_ultrafilter_le (atTop : Filter ℕ)
  have limit (f : ℕ → Bool) : ∃ b, ∀ᶠ j in (U : Filter ℕ), f j = b := by
    have hor : ∀ᶠ j in (U : Filter ℕ), f j = false ∨ f j = true :=
      Eventually.of_forall fun j => (Bool.eq_false_or_eq_true (f j)).symm
    rcases U.eventually_or.mp hor with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  choose d hd using fun i => limit (c i)
  obtain ⟨b, hb⟩ := limit d
  let good (v : ℕ → ℕ) (n j : ℕ) : Prop :=
    d j = b ∧ ∀ i < n, v i < j ∧ c (v i) j = d (v i)
  have exists_good (v : ℕ → ℕ) (n : ℕ) : ∃ j, good v n j := by
    apply Eventually.exists (f := (U : Filter ℕ))
    refine hb.and ?_
    apply (Set.finite_lt_nat n).eventually_all.mpr
    intro i hi
    exact ((eventually_gt_atTop (v i)).filter_mono hU).and (hd (v i))
  let v : ℕ → ℕ := wellFounded_lt.fix fun n prev =>
    (exists_good (fun i => if hi : i < n then prev i hi else 0) n).choose
  have hv (n) : good v n (v n) := by
    let v' : ℕ → ℕ := fun i => if i < n then v i else 0
    have h := (exists_good v' n).choose_spec
    have he : v n = (exists_good v' n).choose := wellFounded_lt.fix_eq _ n
    rw [← he] at h
    refine ⟨h.1, fun i hi => ?_⟩
    simpa only [v', ite_eq_left hi] using h.2 i hi
  exact ⟨v, b, fun _ j hij => ((hv j).2 _ hij).1,
    fun i j hij => (((hv j).2 i hij).2).trans (hv i).1⟩

private theorem mk_iUnion_le_of_countable {α ι : Type} [Countable ι] {κ : Cardinal}
    (hκ : ℵ₀ ≤ κ) (s : ι → Set α) (hs : ∀ i, #(s i) ≤ κ) : #(⋃ i, s i) ≤ κ :=
  (mk_iUnion_le s).trans <|
    (mul_le_mul' (mk_le_aleph0_iff.mpr inferInstance) (ciSup_le' hs)).trans_eq (aleph0_mul_eq hκ)

private structure BlocksAt {α : Type} (c : α → α → Bool) (representative : ℕ → α)
    (A : Set α) (κ : Cardinal) where
  carrier : Bool → Set α
  subset (b : Bool) : carrier b ⊆ A
  card (b : Bool) : #(carrier b) = κ
  mono (b : Bool) : Monochromatic c b (carrier b)
  profile : ℕ → Bool
  agrees (b : Bool) {x : α} (hx : x ∈ carrier b) (j : ℕ) : c x (representative j) = profile j

private theorem exists_blocks {α : Type} {δ : Cardinal}
    (κ : ℕ → Cardinal) (hκ : Monotone κ) (hκ₀ : ∀ i, ℵ₀ ≤ κ i)
    (hκδ : ∀ i, κ i ≤ δ) (hδ : ∀ i, δ ≤ 2 ^ κ i)
    (A : ℕ → Set α) (hA : ∀ i, #(A i) = succ (2 ^ κ i))
    (hpowers : StrictMono fun i => (2 : Cardinal) ^ κ i)
    (c : α → α → Bool) (hc : ∀ x y, c x y = c y x)
    (hno : ¬ ∃ (H : Set α) (b : Bool), δ ≤ #H ∧ Monochromatic c b H) :
    ∃ (B : ℕ → Bool → Set α) (profile : ℕ → ℕ → Bool),
      (∀ i b, #(B i b) = κ i ∧ Monochromatic c b (B i b)) ∧
      ∀ i j, i < j → ∀ b d, ∀ x ∈ B i b, ∀ y ∈ B j d, c x y = profile i j := by
  classical
  let earlier (i : ℕ) : Set α := ⋃ j : Fin i, A j
  have hear (i) : #(earlier i) ≤ 2 ^ κ i := by
    apply mk_iUnion_le_of_countable ((hκ₀ i).trans (cantor _).le)
    intro j
    rw [hA]
    exact succ_le_of_lt (hpowers j.isLt)
  choose representative _ hrep using fun i =>
    exists_representative (hκ₀ i) (hear i) (hA i) c
  let Block (i : ℕ) := BlocksAt c representative (A i) (κ i)
  have next (i) (prev : ∀ j < i, Block j) :
      ∃ B : Block i, ∀ j (hj : j < i) (b d : Bool),
        ∀ x ∈ (prev j hj).carrier b, ∀ y ∈ B.carrier d, c x y = (prev j hj).profile i := by
    let T : Set α := ⋃ j : Fin i, (prev j j.isLt).carrier false ∪ (prev j j.isLt).carrier true
    have hT (j : ℕ) (hj : j < i) (b : Bool) : (prev j hj).carrier b ⊆ T := by
      intro x hx
      apply mem_iUnion.mpr
      refine ⟨⟨j, hj⟩, ?_⟩
      cases b
      · exact Or.inl hx
      · exact Or.inr hx
    have hTS : T ⊆ earlier i := by
      intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      refine mem_iUnion.mpr ⟨j, ?_⟩
      exact hj.elim (fun h => (prev j j.isLt).subset false h)
        (fun h => (prev j j.isLt).subset true h)
    have hcardT : #T ≤ κ i := by
      apply mk_iUnion_le_of_countable (hκ₀ i)
      intro j
      apply (mk_union_le _ _).trans
      rw [(prev j j.isLt).card false, (prev j j.isLt).card true, add_eq_self (hκ₀ j)]
      exact hκ j.isLt.le
    let agreeing : Set α := {x ∈ A i | ∀ z ∈ T, c z x = c z (representative i)}
    have hcardAgree : succ (2 ^ κ i) ≤ #agreeing := hrep i T hTS hcardT
    let toProfile (x : agreeing) (j : ℕ) := c x.val (representative j)
    have hpow₀ : ℵ₀ ≤ (2 : Cardinal) ^ κ i := (hκ₀ i).trans (cantor _).le
    have hreg := isRegular_succ hpow₀
    have hprofiles : #(ℕ → Bool) < (succ ((2 : Cardinal) ^ κ i)).ord.cof := by
      rw [hreg.cof_ord, mk_arrow, lift_id, lift_id, mk_bool, mk_nat]
      exact (power_le_power_left two_ne_zero (hκ₀ i)).trans_lt (lt_succ _)
    obtain ⟨profile, U, hU, hcardU, hagree⟩ :=
      infinite_pigeonhole_set toProfile (succ (2 ^ κ i)) hcardAgree hreg.aleph0_le hprofiles
    have exists_color (b : Bool) :
        ∃ H : Set α, H ⊆ U ∧ #H = κ i ∧ Monochromatic c b H := by
      let c' (x y : U) := c x.val y.val
      have hlarge := exists_large_monochromatic (hκ₀ i) (hκδ i) (hδ i)
        ((lt_succ _).trans_le hcardU) c' (fun x y => hc x.val y.val) b
      have hmono (s : Set U) (d) (hs : Monochromatic c' d s) :
          Monochromatic c d (Subtype.val '' s) := by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
        exact hs hx hy (fun he => hne (congrArg Subtype.val he))
      rcases hlarge with ⟨s, hcard, hs⟩ | ⟨s, hcard, hs⟩
      · exact (hno ⟨Subtype.val '' s, !b,
          hcard.trans_eq (mk_image_eq Subtype.val_injective).symm, hmono s _ hs⟩).elim
      · have he : κ i ≤ #(Subtype.val '' s) :=
          hcard.trans_eq (mk_image_eq Subtype.val_injective).symm
        obtain ⟨H, hH, hcH⟩ := le_mk_iff_exists_subset.mp he
        exact ⟨H, hH.trans (by rintro _ ⟨z, _, rfl⟩; exact z.property), hcH,
          fun x hx y hy hne => hmono s b hs (hH hx) (hH hy) hne⟩
    choose carrier hsub hcard hmono using exists_color
    refine ⟨⟨carrier, fun b => (hsub b).trans (hU.trans fun _ h => h.1),
      hcard, hmono, profile, fun b _ hx j => congrFun (hagree (hsub b hx)) j⟩, ?_⟩
    intro j hj b d x hx y hy
    exact ((hU (hsub d hy)).2 x (hT j hj b hx)).trans ((prev j hj).agrees b hx i)
  let blocks : ∀ i, Block i := wellFounded_lt.fix fun i prev => (next i prev).choose
  refine ⟨fun i => (blocks i).carrier, fun i => (blocks i).profile,
    fun i b => ⟨(blocks i).card b, (blocks i).mono b⟩, ?_⟩
  intro i j hij
  have hj : blocks j = (next j (fun i _ => blocks i)).choose := wellFounded_lt.fix_eq _ j
  have hcross := (next j (fun i _ => blocks i)).choose_spec i hij
  rwa [← hj] at hcross

/--
**Shelah's theorem (Erdős Problem 1219).** For every strictly increasing sequence
$n_0 < n_1 < \cdots$ of natural numbers such that the cardinals $2^{\aleph_{n_k}}$ are strictly
increasing in $k$ and $2^{\aleph_{n_0}} > \aleph_\omega$, the partition relation
$\sum_k 2^{\aleph_{n_k}} \to (\aleph_\omega)^2_2$ holds: for every set $X$ of cardinality
$\sum_k 2^{\aleph_{n_k}}$ and every symmetric colouring of the pairs of elements of $X$ with two
colours, some subset of $X$ of cardinality $\aleph_\omega$ has all pairs of distinct elements of
the same colour.

Source: T. F. Bloom, Erdős Problems, Problem
#1219, https://www.erdosproblems.com/1219 (status PROVED); resolution: S. Shelah, Notes on partition
calculus, in Infinite and Finite Sets (Colloq. Keszthely, 1973), Colloq. Math. Soc. János Bolyai 10,
North-Holland (1975), 1257-1276, erdosproblems.com/1219: proved by Shelah (a problem of Erdős,
Hajnal and Rado; P. Komjáth, The Erdős-Hajnal problem list, Bull. Symb. Log. (2025), p. 2).
-/
public theorem alephOmegaPartitionOfCardinalSum_holds : alephOmegaPartitionOfCardinalSum := by
  classical
  intro n hn hpowers hfirst α hα c hc
  let κ (i : ℕ) : Cardinal := ℵ_ (n i)
  let δ : Cardinal := ℵ_ Ordinal.omega0
  suffices ∃ (H : Set α) (b : Bool), δ ≤ #H ∧ Monochromatic c b H by
    obtain ⟨H, b, hH, hmono⟩ := this
    obtain ⟨T, hT, hcard⟩ := le_mk_iff_exists_subset.mp hH
    exact ⟨T, hcard, b, fun x hx y hy hne => hmono (hT hx) (hT hy) hne⟩
  by_contra hno
  have hκ : Monotone κ := fun i j hij => aleph_le_aleph.mpr (by exact_mod_cast hn.monotone hij)
  have hκδ (i) : κ i ≤ δ := aleph_le_aleph.mpr (Ordinal.natCast_lt_omega0 _).le
  have hδ (i) : δ ≤ (2 : Cardinal) ^ κ i :=
    hfirst.le.trans (hpowers.monotone (Nat.zero_le i))
  have hsize (i) : succ ((2 : Cardinal) ^ κ i) ≤ #α := by
    rw [hα]
    exact (succ_le_of_lt (hpowers (Nat.lt_succ_self i))).trans
      (le_sum (fun j => (2 : Cardinal) ^ κ j) (i + 1))
  choose A hA using fun i => le_mk_iff_exists_set.mp (hsize i)
  obtain ⟨B, profile, hB, hcross⟩ :=
    exists_blocks κ hκ (fun i => aleph0_le_aleph (n i)) hκδ hδ A hA hpowers c hc hno
  obtain ⟨v, b, hv, hprofile⟩ := exists_monochromatic_indices profile
  let H : Set α := ⋃ i, B (v i) b
  refine hno ⟨H, b, ?_, ?_⟩
  · change ℵ_ Ordinal.omega0 ≤ #H
    rw [aleph_limit Ordinal.isSuccLimit_omega0]
    apply ciSup_le'
    intro o
    obtain ⟨i, hi⟩ := Ordinal.lt_omega0.mp o.property
    change ℵ_ (o.val) ≤ _
    rw [hi]
    have hle : i ≤ n (v i) := hv.le_apply.trans hn.le_apply
    calc
      ℵ_ (i : Ordinal) ≤ κ (v i) := aleph_le_aleph.mpr (by exact_mod_cast hle)
      _ = #(B (v i) b) := (hB _ _).1.symm
      _ ≤ #H := mk_le_mk_of_subset (subset_iUnion (fun j => B (v j) b) i)
  · intro x hx y hy hne
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact (hcross _ _ (hv hij) b b x hi y hj).trans (hprofile _ _ hij)
    · exact (hB _ _).2 hi hj hne
    · exact (hc x y).trans ((hcross _ _ (hv hji) b b y hj x hi).trans (hprofile _ _ hji))

end MathlibExt.Combinatorics.AlephOmegaPartitionSumErdosProblem1219Wanted
