/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Classes
import CSLibExt.Computability.Complexity.ACGateBridge
import CSLibExt.Computability.Complexity.CookLevin.Hardness
import Mathlib.Data.Finset.Density
import Mathlib.Data.Fintype.BigOperators
import MathlibExt.Combinatorics.SetFamily.SunflowerLemma

/-!
# Razborov's monotone circuit lower bound for clique

`razborov_monotone_clique` proves that every polynomial gate bound fails for some
`cliqueHolds n`, the clique function with threshold `⌊n/3⌋` on row-major adjacency bits.

The proof uses Razborov's approximation method. On a grid with `t + 1` rows, a positive test
plants a clique using one vertex per row. A negative test joins vertices of different colours
under a colouring with `t` colours. Adding universal vertices gives the required threshold.

Each gate is approximated by a family of vertex sets of bounded size. Dropping large sets costs
little on positive tests. Replacing the petals of a sunflower by their kernel costs little on
negative tests. Folding over the distinct predecessors of each gate takes at most the square
of the circuit size in binary operations. At the output, an empty family rejects every positive
test, while any surviving set accepts most negative tests.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.RazborovMonotoneClique

open Cslib.Complexity.Classes
open Finset MathlibExt.Combinatorics.SetFamily.SunflowerLemma

/-- **The clique function on adjacency-matrix bits.** For a natural number $n$ and a bitstring
$x$, read $x$ as an $n \times n$ adjacency matrix in row-major order: the entry for a pair
$(a, b)$ is the bit of $x$ at position $an + b$, where a position beyond the end of $x$ reads as
false. The clique predicate holds for $n$ and $x$ when there is a set $S$ of exactly
$\lfloor n/3 \rfloor$ vertices among $0, \dots, n - 1$ such that the entry for $(a, b)$ is true
for all distinct $a, b \in S$. -/
def cliqueHolds (n : ℕ) (x : List Bool) : Prop :=
  ∃ S : Finset ℕ, S.card = n / 3 ∧ (∀ v ∈ S, v < n) ∧
    ∀ a ∈ S, ∀ b ∈ S, a ≠ b → x.getD (a * n + b) false = true

variable {V : Type*} [DecidableEq V]

/-- Bounding the density of functions whose values on a fixed set of coordinates are forced
by their other values. -/
private lemma dens_forced [Fintype V] {q : ℕ} (hq : 0 < q) (S : Finset V)
    (E : Finset (V → Fin q))
    (h : ∀ f ∈ E, ∀ g ∈ E, (∀ x ∉ S, f x = g x) → f = g) :
    E.dens * (q : ℚ≥0) ^ S.card ≤ 1 := by
  classical
  have hinj : Function.Injective (fun f : E => fun x : ↥(univ \ S) => f.val x) := by
    intro f g he
    apply Subtype.ext
    apply h _ f.property _ g.property
    intro x hx
    exact congrFun he ⟨x, by simpa using hx⟩
  have hc := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] at hc
  have hcount : E.card * q ^ S.card ≤ q ^ Fintype.card V := calc
    _ ≤ q ^ (univ \ S).card * q ^ S.card := Nat.mul_le_mul_right _ hc
    _ = _ := by rw [← pow_add, card_sdiff_add_card_eq_card (subset_univ S), card_univ]
  rw [dens, div_mul_eq_mul_div, div_le_one]
  · simpa [Fintype.card_fun] using (show (E.card : ℚ≥0) * (q : ℚ≥0) ^ S.card ≤
      q ^ Fintype.card V by exact_mod_cast hcount)
  · simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    positivity

/-- The density of a union of at most `s.card` events. -/
private lemma dens_union_bound {T I : Type*} [Fintype T] [DecidableEq T]
    (s : Finset I) (e : I → Finset T) (b : ℚ≥0) (h : ∀ i ∈ s, (e i).dens ≤ b) :
    (s.biUnion e).dens ≤ s.card * b := by
  rw [dens]
  have hc := @Finset.card_biUnion_le I T _ s e
  calc
    _ ≤ (∑ i ∈ s, ((e i).card : ℚ≥0)) / Fintype.card T := by
      gcongr
      exact_mod_cast hc
    _ = ∑ i ∈ s, (e i).dens := by simp [dens, Finset.sum_div]
    _ ≤ _ := by simpa using (sum_le_sum (s := s) h)

/-- A large family of sets of bounded width contains a sunflower. -/
private lemma bounded_sunflower (w p : ℕ) (F : Finset (Finset V))
    (hw : ∀ A ∈ F, A.card ≤ w)
    (hc : (w + 1) * (w.factorial * p ^ w) < F.card) (hp : 1 ≤ p) :
    ∃ S ⊆ F, S.card = p ∧ IsDeltaSystem S := by
  classical
  have hex : ∃ j ∈ range (w + 1), w.factorial * p ^ w < (F.filter (·.card = j)).card := by
    by_contra! h
    have hcover : F ⊆ (range (w + 1)).biUnion (fun j => F.filter (·.card = j)) :=
      fun A hA => mem_biUnion.mpr ⟨A.card, mem_range.mpr (by have := hw A hA; omega),
        mem_filter.mpr ⟨hA, rfl⟩⟩
    have hh := (card_le_card hcover).trans <|
      card_biUnion_le.trans (sum_le_card_nsmul _ _ _ h)
    simp at hh
    omega
  obtain ⟨j, hj, hcj⟩ := hex
  have hjw : j ≤ w := by simpa using hj
  have hle : j.factorial * (p - 1) ^ j ≤ w.factorial * p ^ w := by
    apply Nat.mul_le_mul (Nat.factorial_le hjw)
    exact (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right hp hjw)
  obtain ⟨S, hS, hcard, hsun⟩ := exists_isDeltaSystem j p (F.filter (·.card = j))
    (fun A hA => (mem_filter.mp hA).2) (hle.trans_lt hcj)
  exact ⟨S, hS.trans (filter_subset _ _), hcard, hsun⟩

private def colourful {q : ℕ} (c : V → Fin q) (S : Finset V) := Set.InjOn c S

open Classical in
/-- If a colouring distinguishes the kernel of a sunflower but none of the petals, then
every petal contributes a collision involving a vertex outside the kernel. -/
private lemma sunflower_error [Fintype V] {q w : ℕ} (hq : 0 < q)
    (S : Finset (Finset V)) (K : Finset V)
    (hs : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = K)
    (hw : ∀ A ∈ S, A.card ≤ w) :
    (univ.filter (fun c : V → Fin q => colourful c K ∧ ∀ A ∈ S, ¬ colourful c A)).dens ≤
      ((w * w : ℕ) : ℚ≥0) ^ S.card / (q : ℚ≥0) ^ S.card := by
  classical
  let P := (A : ↥S) → ↥A.val × ↥A.val
  let u (z : P) (A : ↥S) : V := (z A).1
  let v (z : P) (A : ↥S) : V := (z A).2
  let valid (z : P) := (∀ A, u z A ∉ K ∧ u z A ≠ v z A)
  let E (z : P) : Finset (V → Fin q) := univ.filter
    (fun c => valid z ∧ ∀ A, c (u z A) = c (v z A))
  have cover : univ.filter (fun c : V → Fin q => colourful c K ∧ ∀ A ∈ S, ¬ colourful c A) ⊆
      (univ : Finset P).biUnion E := by
    intro c hc
    obtain ⟨hK, hS⟩ := (mem_filter.mp hc).2
    have pick (A : ↥S) : ∃ a b : ↥A.val, a.val ∉ K ∧ a.val ≠ b.val ∧ c a = c b := by
      have hn := hS A.val A.property
      simp only [colourful, Set.InjOn, not_forall] at hn
      obtain ⟨a, ha, b, hb, he, hne⟩ := hn
      by_cases hk : a ∈ K
      · exact ⟨⟨b, hb⟩, ⟨a, ha⟩, fun hbK => hne (hK hk hbK he), Ne.symm hne, he.symm⟩
      · exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hk, hne, he⟩
    choose a b hk hn he using pick
    exact mem_biUnion.mpr ⟨(fun A => (a A, b A)), mem_univ _,
      mem_filter.mpr ⟨mem_univ _, fun A => ⟨hk A, hn A⟩, he⟩⟩
  have bound (z : P) : (E z).dens ≤ 1 / (q : ℚ≥0) ^ S.card := by
    by_cases hz : valid z
    · have outside {A B : ↥S} (hne : A ≠ B) : u z A ∉ B.val := by
        intro h
        apply (hz A).1
        rw [← hs A A.property B B.property (fun he => hne (Subtype.ext he))]
        exact mem_inter.mpr ⟨(z A).1.property, h⟩
      have hu : Function.Injective (u z) := by
        intro A B he
        by_contra hn
        exact outside hn (he ▸ (z B).1.property)
      let D := (univ : Finset ↥S).image (u z)
      have hv (B : ↥S) : v z B ∉ D := by
        rintro h
        obtain ⟨A, -, he⟩ := mem_image.mp h
        by_cases hab : A = B
        · exact (hz B).2 (hab ▸ he)
        · exact outside hab (he ▸ (z B).2.property)
      have hh := dens_forced hq D (E z) (by
        intro f hf g hg he
        funext x
        by_cases hx : x ∈ D
        · obtain ⟨A, -, rfl⟩ := mem_image.mp hx
          rw [((mem_filter.mp hf).2.2 A), ((mem_filter.mp hg).2.2 A), he _ (hv A)]
        · exact he x hx)
      have hd : D.card = S.card := by simp [D, card_image_of_injective _ hu]
      apply (le_div_iff₀ (by positivity)).2
      rwa [hd] at hh
    · have hem : E z = ∅ := by simp [E, hz]
      simp [hem]
  have hP : Fintype.card P ≤ (w * w) ^ S.card := by
    simp only [P, Fintype.card_pi, Fintype.card_prod, Fintype.card_coe]
    calc
      _ ≤ ∏ _ : ↥S, w * w :=
        prod_le_prod (fun i _ => Nat.mul_le_mul (hw i i.property) (hw i i.property))
      _ = _ := by simp
  calc
    _ ≤ ((univ : Finset P).biUnion E).dens := dens_le_dens cover
    _ ≤ _ := dens_union_bound univ E _ (fun z _ => bound z)
    _ ≤ ((w * w : ℕ) : ℚ≥0) ^ S.card / (q : ℚ≥0) ^ S.card := by
      rw [card_univ, mul_one_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hP) (by positivity)

private abbrev Family (V : Type*) := Finset (Finset V)
private def accepts (F : Family V) (a : Finset V → Prop) := ∃ A ∈ F, a A
private def cap (w : ℕ) := (w + 1) * (w.factorial * w ^ w)
private def negCost (w q : ℕ) : ℚ≥0 := ((w * w : ℕ) : ℚ≥0) ^ w / (q : ℚ≥0) ^ w
open Classical in
private noncomputable def gain [Fintype V] (F G : Family V) (q : ℕ) : Finset (V → Fin q) :=
  univ.filter (fun c => accepts G (colourful c) ∧ ¬ accepts F (colourful c))

/-- Replace sunflowers by their kernels until the family is small. Each replacement removes
at least one term and preserves a subset of every old term. -/
private lemma compress [Fintype V] (w q : ℕ) (hq : 0 < q) (hw : 2 ≤ w)
    (F : Family V) (hF : ∀ A ∈ F, A.card ≤ w) :
    ∃ G : Family V, G.card ≤ cap w ∧ (∀ A ∈ G, A.card ≤ w) ∧
      (∀ A ∈ F, ∃ B ∈ G, B ⊆ A) ∧ (gain F G q).dens ≤ F.card * negCost w q := by
  classical
  by_cases hbig : cap w < F.card
  · obtain ⟨S, hS, hSw, K, hs⟩ := bounded_sunflower w w F hF hbig (by omega)
    have hother (A : Finset V) (hA : A ∈ S) : ∃ B ∈ S, B ≠ A := by
      by_contra! he
      have hl := card_le_card (show S ⊆ {A} from fun B hB => mem_singleton.mpr (he B hB))
      simp at hl
      omega
    have hK (A : Finset V) (hA : A ∈ S) : K ⊆ A := by
      obtain ⟨B, hB, hne⟩ := hother A hA
      rw [← hs A hA B hB hne.symm]
      exact inter_subset_left
    let F' := insert K (F \ S)
    have hsmall : F'.card + 1 ≤ F.card := by
      have h₁ := card_insert_le K (F \ S)
      have h₂ := card_sdiff_add_card_eq_card hS
      dsimp [F']
      omega
    have hF' : ∀ A ∈ F', A.card ≤ w := by
      intro A hA
      obtain rfl | ha := mem_insert.mp hA
      · obtain ⟨B, hB⟩ := card_pos.mp (show 0 < S.card by omega)
        exact (card_le_card (hK B hB)).trans (hF _ (hS hB))
      · exact hF _ (mem_sdiff.mp ha).1
    obtain ⟨G, hGc, hGw, hGsub, hGe⟩ := compress w q hq hw F' hF'
    refine ⟨G, hGc, hGw, ?_, ?_⟩
    · intro A ha
      by_cases has : A ∈ S
      · obtain ⟨B, hB, hBK⟩ := hGsub K (mem_insert_self ..)
        exact ⟨B, hB, hBK.trans (hK A has)⟩
      · exact hGsub A (mem_insert_of_mem (mem_sdiff.mpr ⟨ha, has⟩))
    · let err := univ.filter (fun c : V → Fin q => colourful c K ∧ ∀ A ∈ S, ¬ colourful c A)
      have he : (gain F G q) ⊆ gain F' G q ∪ err := by
        intro c hc
        obtain ⟨hg, hf⟩ := (mem_filter.mp hc).2
        rw [mem_union]
        by_cases ha : accepts F' (colourful c)
        · right
          obtain ⟨A, hA, hcol⟩ := ha
          obtain rfl | h := mem_insert.mp hA
          · exact mem_filter.mpr ⟨mem_univ _, hcol, fun A hA hc => hf ⟨A, hS hA, hc⟩⟩
          · exact False.elim (hf ⟨A, (mem_sdiff.mp h).1, hcol⟩)
        · left; exact mem_filter.mpr ⟨mem_univ _, hg, ha⟩
      have hstep : err.dens ≤ negCost w q := by
        simpa [err, negCost, hSw] using sunflower_error hq S K hs (fun A hA => hF _ (hS hA))
      calc
        _ ≤ _ := dens_le_dens he
        _ ≤ _ := dens_union_le _ _
        _ ≤ (F'.card : ℚ≥0) * negCost w q + negCost w q := add_le_add hGe hstep
        _ = (F'.card + 1 : ℚ≥0) * negCost w q := by ring
        _ ≤ _ := by gcongr; exact_mod_cast hsmall
  · refine ⟨F, by omega, hF, fun A ha => ⟨A, ha, Subset.rfl⟩, ?_⟩
    simp [gain]
termination_by F.card

private def selected {r b : ℕ} (f : Fin r → Fin b) (A : Finset (Fin r × Fin b)) :=
  ∀ v ∈ A, f v.1 = v.2

open Classical in
private lemma selected_rare {r b w : ℕ} (hb : 0 < b) (A : Finset (Fin r × Fin b))
    (hA : w ≤ A.card) :
    (univ.filter (fun f : Fin r → Fin b => selected f A)).dens ≤ 1 / (b : ℚ≥0) ^ w := by
  classical
  let E := univ.filter (fun f : Fin r → Fin b => selected f A)
  by_cases hne : E.Nonempty
  · obtain ⟨f, hf⟩ := hne
    have hsel := (mem_filter.mp hf).2
    have hinj : Set.InjOn Prod.fst (A : Set (Fin r × Fin b)) := by
      intro x hx y hy he
      exact Prod.ext he ((hsel x hx).symm.trans ((congrArg f he).trans (hsel y hy)))
    have hh := dens_forced hb (A.image Prod.fst) E (by
      intro f hf g hg he
      funext i
      by_cases hi : i ∈ A.image Prod.fst
      · obtain ⟨v, hv, rfl⟩ := mem_image.mp hi
        exact ((mem_filter.mp hf).2 v hv).trans ((mem_filter.mp hg).2 v hv).symm
      · exact he i hi)
    apply (le_div_iff₀ (by positivity)).2
    rw [card_image_of_injOn hinj] at hh
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by exact_mod_cast hb) hA)
      (by positivity)).trans hh
  · have he := not_nonempty_iff_eq_empty.mp hne
    change E.dens ≤ _
    simp [he]

private abbrev Vertex (t : ℕ) := Fin (t + 1) × Fin (2 * t + 3)
private abbrev PosTest (t : ℕ) := Fin (t + 1) → Fin (2 * t + 3)
private abbrev NegTest (t : ℕ) := Vertex t → Fin t
private abbrev Sample (t : ℕ) := PosTest t × NegTest t
private abbrev Errors (t : ℕ) := Finset (Sample t)

private structure Approx (t w : ℕ) where
  terms : Family (Vertex t)
  small : terms.card ≤ cap w
  narrow : ∀ A ∈ terms, A.card ≤ w

/-- Outside the exceptional set an approximator must preserve true positive outputs and
reflect true negative-test outputs. -/
private def fits {t : ℕ} (F : Family (Vertex t)) (s : Sample t) (p n : Prop) :=
  (p → accepts F (selected s.1)) ∧ (accepts F (colourful s.2) → n)

private def stepSize (w : ℕ) := (cap w + 1) ^ 2
private def stepNumer (w : ℕ) := stepSize w * (1 + (w * w) ^ w)
private def stepCost (t w : ℕ) : ℚ≥0 := stepNumer w / (t : ℚ≥0) ^ w

private lemma dens_prod {P N : Type*} [Fintype P] [Fintype N] (a : Finset P) (b : Finset N) :
    (a ×ˢ b).dens = a.dens * b.dens := by
  simp [dens, div_mul_div_comm]

/-- Truncation and sunflower compression contribute errors on opposite test distributions. -/
private lemma roundFamily {t w : ℕ} (ht : 0 < t) (hw : 2 ≤ w) (F : Family (Vertex t))
    (hc : F.card ≤ stepSize w) :
    ∃ (G : Approx t w) (E : Errors t), E.dens ≤ stepCost t w ∧
      ∀ s ∉ E, fits G.terms s (accepts F (selected s.1)) (accepts F (colourful s.2)) := by
  classical
  let T := F.filter (·.card ≤ w)
  obtain ⟨G, hGc, hGw, hsub, herr⟩ := compress w t ht hw T (fun A hA => (mem_filter.mp hA).2)
  let dropped := F.filter (w < ·.card)
  let P : Finset (PosTest t) := dropped.biUnion (fun A => univ.filter (selected · A))
  let N := gain T G t
  let E : Errors t := (P ×ˢ univ) ∪ (univ ×ˢ N)
  refine ⟨⟨G, hGc, hGw⟩, E, ?_, ?_⟩
  · have hb : (t : ℚ≥0) ^ w ≤ ((2 * t + 3 : ℕ) : ℚ≥0) ^ w := by
      gcongr
      exact_mod_cast (show t ≤ 2 * t + 3 by omega)
    have hP : P.dens ≤ (stepSize w : ℚ≥0) / (t : ℚ≥0) ^ w := calc
      _ ≤ dropped.card * (1 / (t : ℚ≥0) ^ w) := dens_union_bound _ _ _ (by
        intro A hA
        apply (selected_rare (by omega) A (Nat.le_of_lt (mem_filter.mp hA).2)).trans
        gcongr)
      _ ≤ _ := by
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right (by exact_mod_cast (card_filter_le ..).trans hc)
          (by positivity)
    have hN : N.dens ≤ (stepSize w : ℚ≥0) * negCost w t :=
      herr.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast (card_filter_le ..).trans hc)
        (by positivity))
    calc
      E.dens ≤ _ := dens_union_le _ _
      _ ≤ P.dens + N.dens := by
        rw [dens_prod, dens_prod]
        exact add_le_add (mul_le_of_le_one_right (by positivity) dens_le_one)
          (mul_le_of_le_one_left (by positivity) dens_le_one)
      _ ≤ _ := add_le_add hP hN
      _ = stepCost t w := by simp [negCost, stepCost, stepNumer]; ring
  · intro s he
    have hp : s.1 ∉ P := fun h => he (mem_union_left _ (mk_mem_product h (mem_univ _)))
    have hn : s.2 ∉ N := fun h => he (mem_union_right _ (mk_mem_product (mem_univ _) h))
    constructor
    · rintro ⟨A, hA, hsel⟩
      have hAw : A.card ≤ w := by
        by_contra! h
        exact hp (mem_biUnion.mpr ⟨A, mem_filter.mpr ⟨hA, h⟩, mem_filter.mpr ⟨mem_univ _, hsel⟩⟩)
      obtain ⟨B, hB, hBA⟩ := hsub A (mem_filter.mpr ⟨hA, hAw⟩)
      exact ⟨B, hB, fun v hv => hsel v (hBA hv)⟩
    · intro hG
      by_contra hF
      apply hn (mem_filter.mpr ⟨mem_univ _, hG, ?_⟩)
      exact fun ⟨A, hA, ha⟩ => hF ⟨A, (mem_filter.mp hA).1, ha⟩

private def combine (conj : Bool) (p q : Prop) := if conj then p ∧ q else p ∨ q

private lemma combine_mono (c : Bool) {p q p' q' : Prop} (hp : p → p') (hq : q → q') :
    combine c p q → combine c p' q' := by
  cases c <;> simp only [combine, Bool.false_eq_true, ite_false, ite_true]
  · exact Or.imp hp hq
  · exact And.imp hp hq

private lemma binary {t w : ℕ} (ht : 0 < t) (hw : 2 ≤ w) (c : Bool) (A B : Approx t w) :
    ∃ (G : Approx t w) (E : Errors t), E.dens ≤ stepCost t w ∧ ∀ s ∉ E,
      fits G.terms s (combine c (accepts A.terms (selected s.1)) (accepts B.terms (selected s.1)))
        (combine c (accepts A.terms (colourful s.2)) (accepts B.terms (colourful s.2))) := by
  classical
  cases c
  · obtain ⟨G, E, he, hG⟩ := roundFamily ht hw (A.terms ∪ B.terms) (by
      apply (card_union_le _ _).trans
      have := A.small
      have := B.small
      dsimp [stepSize]
      nlinarith)
    refine ⟨G, E, he, fun s hs => ?_⟩
    simpa [fits, combine, accepts, or_and_right, exists_or] using hG s hs
  · let F := (A.terms ×ˢ B.terms).image (fun (a, b) => a ∪ b)
    obtain ⟨G, E, he, hG⟩ := roundFamily ht hw F (by
      apply card_image_le.trans
      rw [card_product]
      exact (Nat.mul_le_mul A.small B.small).trans (by dsimp [stepSize]; nlinarith))
    refine ⟨G, E, he, fun s hs => ⟨?_, ?_⟩⟩
    · rintro ⟨⟨a, ha, hsa⟩, ⟨b, hb, hsb⟩⟩
      apply (hG s hs).1
      exact ⟨a ∪ b, mem_image.mpr ⟨(a, b), mk_mem_product ha hb, rfl⟩, fun v hv =>
        (mem_union.mp hv).elim (hsa v) (hsb v)⟩
    · intro hg
      obtain ⟨U, hU, hc⟩ := (hG s hs).2 hg
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.mp hU
      exact ⟨⟨a, (mem_product.mp hab).1, hc.mono (by exact_mod_cast (subset_union_left (s₂ := b)))⟩,
        ⟨b, (mem_product.mp hab).2, hc.mono (by exact_mod_cast (subset_union_right (s₁ := a)))⟩⟩

private lemma cap_pos {w : ℕ} (hw : 2 ≤ w) : 0 < cap w := by
  dsimp [cap]
  have := Nat.factorial_pos w
  positivity

private def constant {t w : ℕ} (hw : 2 ≤ w) (c : Bool) : Approx t w where
  terms := if c then {∅} else ∅
  small := by cases c <;> simp [Nat.succ_le_iff, cap_pos hw]
  narrow := by cases c <;> simp

private lemma constant_fits {t w : ℕ} (hw : 2 ≤ w) (c : Bool) (s : Sample t) :
    fits (constant hw c).terms s (c = true) (c = true) := by
  cases c <;> simp [fits, constant, accepts, selected, colourful]

private def aggregate (c : Bool) (J : Finset ℕ) (p : ℕ → Prop) :=
  if c then ∀ j ∈ J, p j else ∃ j ∈ J, p j

private lemma aggregate_mono (c : Bool) (J : Finset ℕ) {p q : ℕ → Prop}
    (h : ∀ j ∈ J, p j → q j) : aggregate c J p → aggregate c J q := by
  cases c
  · exact fun ⟨j, hj, hp⟩ => ⟨j, hj, h j hj hp⟩
  · exact fun hp j hj => h j hj (hp j hj)

private lemma aggregate_insert (c : Bool) (j : ℕ) (J : Finset ℕ) (p : ℕ → Prop) :
    aggregate c (insert j J) p ↔ combine c (p j) (aggregate c J p) := by
  cases c <;> simp [aggregate, combine]

private lemma foldApprox {t w : ℕ} (ht : 0 < t) (hw : 2 ≤ w) (c : Bool)
    (J : Finset ℕ) (A : ℕ → Approx t w) :
    ∃ (G : Approx t w) (E : Errors t), E.dens ≤ J.card * stepCost t w ∧ ∀ s ∉ E,
      fits G.terms s (aggregate c J (fun j => accepts (A j).terms (selected s.1)))
        (aggregate c J (fun j => accepts (A j).terms (colourful s.2))) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    refine ⟨constant hw c, ∅, by simp, fun s _ => ?_⟩
    have h := constant_fits hw c s
    cases c <;> simpa [aggregate] using h
  | insert j J hj ih =>
    obtain ⟨B, E, he, hb⟩ := ih
    obtain ⟨G, D, hd, hg⟩ := binary ht hw c (A j) B
    refine ⟨G, E ∪ D, ?_, fun s hs => ?_⟩
    · apply (dens_union_le _ _).trans ((add_le_add he hd).trans ?_)
      rw [card_insert_of_notMem hj, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    · rw [mem_union, not_or] at hs
      simp_rw [aggregate_insert]
      exact ⟨(hg s hs.2).1 ∘ combine_mono c id (hb s hs.1).1,
        combine_mono c id (hb s hs.1).2 ∘ (hg s hs.2).2⟩

private def fanGate {n : ℕ} (c : Bool) (l : List ℕ) : ACGate n :=
  if c then .andGate l else .orGate l

private lemma fanGate_value {n : ℕ} (c : Bool) (l : List ℕ) (v : List Bool) (a : Fin n → Bool) :
    gateValue v a (fanGate c l) = true ↔ aggregate c l.toFinset (fun j => v.getD j false) := by
  cases c <;> simp [fanGate, gateValue, aggregate]

/-- One exceptional set works simultaneously for every wire. At a new gate the old errors
are already covered, so the union bound charges only its distinct predecessors. -/
private lemma approxCircuit {m t w : ℕ} (ht : 0 < t) (hw : 2 ≤ w)
    (pa : PosTest t → Fin m → Bool) (na : NegTest t → Fin m → Bool)
    (input : Fin m → Approx t w) (hi : ∀ i (s : Sample t),
      fits (input i).terms s (pa s.1 i) (na s.2 i))
    (C : List (ACGate m)) (hwf : WellFormedCircuit C) (hm : IsMonotoneCircuit C) :
    ∃ (A : ℕ → Approx t w) (E : Errors t), E.dens ≤ (C.length : ℚ≥0) ^ 2 * stepCost t w ∧
      ∀ s ∉ E, ∀ j < C.length, fits (A j).terms s
        ((circuitEval C (pa s.1)).getD j false) ((circuitEval C (na s.2)).getD j false) := by
  classical
  induction C using List.reverseRecOn with
  | nil => exact ⟨fun _ => constant hw false, ∅, by simp, by simp⟩
  | append_singleton C g ih =>
    have hwfC : WellFormedCircuit C := by
      intro j hj
      have h := hwf j (by simp; omega)
      rwa [List.getElem_append_left hj] at h
    have hmC : IsMonotoneCircuit C := fun h hh => hm h (by simp [hh])
    obtain ⟨A, E, hE, hA⟩ := ih hwfC hmC
    have hpred (j : ℕ) (hj : j ∈ gateInputs g) : j < C.length := by
      apply hwf C.length (by simp)
      simpa using hj
    have hfan (c : Bool) (l : List ℕ) (h : g = fanGate c l) :
        ∃ (G : Approx t w) (D : Errors t), D.dens ≤ C.length * stepCost t w ∧
          ∀ s ∉ E ∪ D, fits G.terms s (gateValue (circuitEval C (pa s.1)) (pa s.1) g)
            (gateValue (circuitEval C (na s.2)) (na s.2) g) := by
      have hre (j : ℕ) (hj : j ∈ l.toFinset) : j < C.length := by
        apply hpred j
        cases c <;> simpa [h, fanGate, gateInputs] using hj
      obtain ⟨G, D, hd, hg⟩ := foldApprox ht hw c l.toFinset A
      refine ⟨G, D, hd.trans ?_, fun s hs => ?_⟩
      · have : l.toFinset ⊆ range C.length := fun j hj => mem_range.mpr (hre j hj)
        gcongr
        simpa using card_le_card this
      · rw [mem_union, not_or] at hs
        simp only [fits, h, fanGate_value]
        exact ⟨(hg s hs.2).1 ∘ aggregate_mono _ _ (fun j hj => (hA s hs.1 j (hre j hj)).1),
          aggregate_mono _ _ (fun j hj => (hA s hs.1 j (hre j hj)).2) ∘ (hg s hs.2).2⟩
    have hgate : ∃ (G : Approx t w) (D : Errors t), D.dens ≤ C.length * stepCost t w ∧
        ∀ s ∉ E ∪ D, fits G.terms s (gateValue (circuitEval C (pa s.1)) (pa s.1) g)
          (gateValue (circuitEval C (na s.2)) (na s.2) g) := by
      have hg := hm g (List.mem_append_right _ (List.mem_singleton_self _))
      cases g with
      | var i => exact ⟨input i, ∅, by simp, fun s _ => hi i s⟩
      | andGate l => exact hfan true l rfl
      | orGate l => exact hfan false l rfl
      | const | notGate | modGate => exact hg.elim
    obtain ⟨G, D, hd, hG⟩ := hgate
    refine ⟨Function.update A C.length G, E ∪ D, ?_, ?_⟩
    · apply (dens_union_le _ _).trans ((add_le_add hE hd).trans ?_)
      rw [← add_mul]
      simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (show C.length ^ 2 + C.length ≤ (C.length + 1) ^ 2 by nlinarith)
    · intro s hs j hj
      rw [circuitEval_append_singleton, circuitEval_append_singleton]
      have hlt : j ≤ C.length := by simpa using hj
      rcases hlt.lt_or_eq with hj | rfl
      · rw [Function.update_of_ne hj.ne, List.getD_append _ _ _ _ (by simpa),
            List.getD_append _ _ _ _ (by simpa)]
        exact hA s (fun h => hs (mem_union_left _ h)) j hj
      · rw [Function.update_self, List.getD_append_right _ _ _ _ (by simp),
            List.getD_append_right _ _ _ _ (by simp)]
        simpa [length_circuitEval] using hG s hs

/-- The left summand consists of universal vertices. There are exactly enough to complete
a transversal of the grid to a clique on one third of the vertices. -/
private abbrev Node (t : ℕ) := Fin (t * (t + 1)) ⊕ Vertex t
private abbrev nodeCount (t : ℕ) := Fintype.card (Node t)

private lemma nodeCount_eq (t : ℕ) : nodeCount t = 3 * (t + 1) ^ 2 := by
  simp [nodeCount, Node, Vertex]
  ring

private lemma threshold (t : ℕ) : nodeCount t / 3 = t * (t + 1) + (t + 1) := by
  rw [nodeCount_eq, Nat.mul_div_cancel_left _ (by decide : 0 < 3)]
  ring

private def edgeTerm {t : ℕ} : Node t → Node t → Finset (Vertex t)
  | .inr u, .inr v => {u, v}
  | _, _ => ∅

private noncomputable def indexedEdge {t : ℕ} (i : Fin (nodeCount t * nodeCount t)) :
    Finset (Vertex t) :=
  let (a, b) := finProdFinEquiv.symm i
  edgeTerm ((Fintype.equivFin _).symm a) ((Fintype.equivFin _).symm b)

open Classical in
private noncomputable def matrix {t : ℕ} (test : Finset (Vertex t) → Prop) : List Bool :=
  List.ofFn (fun i : Fin (nodeCount t * nodeCount t) => decide (test (indexedEdge i)))

private lemma matrix_get {t : ℕ} (test : Finset (Vertex t) → Prop)
    (i : Fin (nodeCount t * nodeCount t)) :
    (matrix test).getD i false = true ↔ test (indexedEdge i) := by
  rw [List.getD_eq_getElem _ _ (by simpa only [matrix, List.length_ofFn] using i.isLt)]
  simp only [matrix, List.getElem_ofFn, Fin.eta, decide_eq_true_eq]

private lemma matrix_bit {t : ℕ} (test : Finset (Vertex t) → Prop) (u v : Node t) :
    (matrix test).getD ((Fintype.equivFin _ u).val * nodeCount t + (Fintype.equivFin _ v).val)
      false = true ↔ test (edgeTerm u v) := by
  let i := finProdFinEquiv (Fintype.equivFin _ u, Fintype.equivFin _ v)
  have hi : i.val = (Fintype.equivFin _ u).val * nodeCount t + (Fintype.equivFin _ v).val := by
    dsimp [i, finProdFinEquiv]
    ring
  rw [← hi, matrix_get]
  simp only [i, indexedEdge, Equiv.symm_apply_apply]

private def positiveVertex {t : ℕ} (f : PosTest t) :
    Fin (t * (t + 1)) ⊕ Fin (t + 1) → Node t :=
  Sum.map id (fun i => (i, f i))

private lemma positive_clique {t : ℕ} (f : PosTest t) :
    cliqueHolds (nodeCount t) (matrix (selected f)) := by
  classical
  let v := fun i => (Fintype.equivFin _ (positiveVertex f i)).val
  have hinj : Function.Injective v := by
    apply Fin.val_injective.comp
    apply (Fintype.equivFin _).injective.comp
    exact Sum.map_injective.mpr ⟨Function.injective_id, fun _ _ h => congrArg Prod.fst h⟩
  refine ⟨univ.image v, ?_, ?_, ?_⟩
  · rw [threshold]
    simp [card_image_of_injective _ hinj]
  · intro a ha
    obtain ⟨i, -, rfl⟩ := mem_image.mp ha
    exact (Fintype.equivFin _ _).isLt
  · intro a ha b hb _
    obtain ⟨i, -, rfl⟩ := mem_image.mp ha
    obtain ⟨j, -, rfl⟩ := mem_image.mp hb
    apply (matrix_bit _ _ _).2
    cases i <;> cases j <;> simp [positiveVertex, edgeTerm, selected]

private lemma negative_clique {t : ℕ} (c : NegTest t) :
    ¬cliqueHolds (nodeCount t) (matrix (colourful c)) := by
  classical
  rintro ⟨S, hSc, hSn, hcl⟩
  let node (a : S) := (Fintype.equivFin (Node t)).symm ⟨a.val, hSn a a.property⟩
  have hnode (a : S) : (Fintype.equivFin _ (node a)).val = a.val := by simp [node]
  have hcol {a b : S} (hne : a ≠ b) : colourful c (edgeTerm (node a) (node b)) := by
    apply (matrix_bit _ _ _).1
    rw [hnode, hnode]
    exact hcl a a.property b b.property (fun h => hne (Subtype.ext h))
  let col : Node t → Fin (t * (t + 1)) ⊕ Fin t := Sum.map id c
  have hinj : Function.Injective (col ∘ node) := by
    intro a b hab
    by_contra hne
    have hc := hcol hne
    apply hne
    apply Subtype.ext
    rw [← hnode a, ← hnode b]
    apply congrArg (fun x : Node t => (Fintype.equivFin _ x).val)
    change col (node a) = col (node b) at hab
    cases h₁ : node a with
    | inl i => cases h₂ : node b <;> simp_all [col]
    | inr i =>
      cases h₂ : node b with
      | inl j => simp [h₁, h₂, col] at hab
      | inr j =>
        simp only [h₁, h₂, col, Sum.map_inr, Sum.inr.injEq] at hab
        rw [h₁, h₂] at hc
        exact congrArg Sum.inr (hc (by simp [edgeTerm]) (by simp [edgeTerm]) hab)
  have hh := Fintype.card_le_of_injective _ hinj
  rw [threshold] at hSc
  simp [hSc] at hh

private noncomputable def inputApprox {t w : ℕ} (hw : 2 ≤ w)
    (i : Fin (nodeCount t * nodeCount t)) : Approx t w where
  terms := {indexedEdge i}
  small := by rw [card_singleton]; exact cap_pos hw
  narrow := by
    simp only [mem_singleton]
    rintro A rfl
    have bound (u v : Node t) : (edgeTerm u v).card ≤ w := by
      cases u <;> cases v <;> simp only [edgeTerm, card_empty, Nat.zero_le]
      exact (card_insert_le ..).trans (by simpa only [card_singleton] using hw)
    exact bound _ _

private lemma input_fits {t w : ℕ} (hw : 2 ≤ w) (i : Fin (nodeCount t * nodeCount t))
    (s : Sample t) : fits (inputApprox hw i).terms s
      ((matrix (selected s.1)).getD i false) ((matrix (colourful s.2)).getD i false) := by
  simp only [fits, matrix_get]
  simp [inputApprox, accepts]

open Classical in
/-- A nonempty family has a term that accepts most negative tests. Apply the collision estimate
to the sunflower with this single petal and empty kernel. -/
private lemma collision_bound {t w : ℕ} (ht : 0 < t) (A : Finset (Vertex t)) (hA : A.card ≤ w) :
    (univ.filter (fun c : NegTest t => ¬ colourful c A)).dens ≤ (w * w : ℕ) / (t : ℚ≥0) := by
  have h := sunflower_error ht {A} ∅ (w := w) (by simp) (by simpa using hA)
  convert h using 1
  · congr 1
    ext c
    rw [mem_filter, mem_filter]
    simp [colourful]
  · simp

private lemma output_obstruction {t w : ℕ} (ht : 2 * (w * w) < t) (A : Approx t w)
    (E : Errors t) (he : E.dens < 1 / 2) (h : ∀ s ∉ E, fits A.terms s True False) : False := by
  classical
  have hpos : 0 < t := by omega
  let : NeZero t := ⟨hpos.ne'⟩
  obtain ⟨s, hs⟩ : ∃ s : Sample t, s ∉ E := by
    by_contra! hall
    have hu : E = univ := eq_univ_of_forall hall
    simp [hu] at he
    norm_num at he
  obtain ⟨U, hU, -⟩ := (h s hs).1 trivial
  let bad := univ.filter (fun c : NegTest t => ¬ colourful c U)
  have hb : bad.dens < 1 / 2 := (collision_bound hpos U (A.narrow U hU)).trans_lt (by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    rw [one_mul, mul_comm]
    exact_mod_cast ht)
  have hcover : univ ⊆ E ∪ (univ ×ˢ bad) := by
    intro z _
    by_cases hz : z ∈ E
    · exact mem_union_left _ hz
    · exact mem_union_right _ (mk_mem_product (mem_univ _) (mem_filter.mpr ⟨mem_univ _,
        fun hc => (h z hz).2 ⟨U, hU, hc⟩⟩))
  have hh := (dens_le_dens hcover).trans (dens_union_le _ _)
  rw [dens_univ, dens_prod, dens_univ, one_mul] at hh
  have := lt_of_le_of_lt hh (add_lt_add he hb)
  norm_num at this

private lemma output_getD (l : List Bool) :
    l.getD (l.length - 1) false = true ↔ l.getLast? = some true := by
  rw [List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]
  cases l[l.length - 1]? <;> simp

private lemma error_is_large {t w : ℕ} (ht : 2 * (w * w) < t) (hw : 2 ≤ w)
    (C : List (ACGate (nodeCount t * nodeCount t))) (hwf : WellFormedCircuit C)
    (hm : IsMonotoneCircuit C)
    (correct : ∀ x : List Bool, x.length = nodeCount t * nodeCount t →
      ((circuitEval C (fun i => x.getD (i : ℕ) false)).getLast? = some true ↔
        cliqueHolds (nodeCount t) x)) :
    1 / 2 ≤ (C.length : ℚ≥0) ^ 2 * stepCost t w := by
  classical
  by_contra! herr
  let pa (f : PosTest t) (i : Fin (nodeCount t * nodeCount t)) :=
    (matrix (selected f)).getD i false
  let na (c : NegTest t) (i : Fin (nodeCount t * nodeCount t)) :=
    (matrix (colourful c)).getD i false
  have pos (f : PosTest t) : (circuitEval C (pa f)).getLast? = some true :=
    (correct (matrix (selected f)) (List.length_ofFn ..)).2 (positive_clique f)
  have neg (c : NegTest t) : (circuitEval C (na c)).getLast? ≠ some true :=
    fun h => negative_clique c ((correct (matrix (colourful c)) (List.length_ofFn ..)).1 h)
  have hC : C ≠ [] := by
    intro hem
    have hp := pos (fun _ => 0)
    simp [hem, circuitEval] at hp
  obtain ⟨A, E, he, hA⟩ := approxCircuit (by omega) hw pa na (inputApprox hw)
    (input_fits hw) C hwf hm
  apply output_obstruction ht (A (C.length - 1)) E (he.trans_lt herr)
  intro s hs
  have hl : C.length - 1 < C.length := by have := List.length_pos_iff.mpr hC; omega
  have hg := hA s hs (C.length - 1) hl
  have hout (a) := output_getD (circuitEval C a)
  simp only [length_circuitEval] at hout
  exact ⟨fun _ => hg.1 ((hout _).2 (pos s.1)), fun hn => neg s.2 ((hout _).1 (hg.2 hn))⟩

/-- Fix the width after choosing the polynomial, then enlarge the grid. Its growing number of
colours makes the total approximation error small even with a fixed number of petals. -/
private lemma parameters (p : Polynomial ℕ) : ∃ t w : ℕ, 2 ≤ w ∧ 2 * (w * w) < t ∧
    ((p.eval (nodeCount t * nodeCount t) : ℕ) : ℚ≥0) ^ 2 * stepCost t w < 1 / 2 := by
  let P : Polynomial ℕ := (p.comp ((3 * (Polynomial.X + 1) ^ 2) ^ 2)) ^ 2
  obtain ⟨c, e, hc, hp⟩ := Cslib.Complexity.CookLevin.Hardness.eval_le_pow P
  let w := 2 * e + 2
  let t := c + 2 * (w * w) + 2 * stepNumer w + 2
  have ht : 2 ≤ t := by dsimp [t]; omega
  have hbase : t + c ≤ t ^ 2 := calc
    _ ≤ t + t := by dsimp [t]; omega
    _ = 2 * t := by ring
    _ ≤ _ := by rw [sq]; gcongr
  have hder : P.eval t ≤ t ^ (2 * e) :=
    (hp t).trans (by rw [pow_mul]; exact Nat.pow_le_pow_left hbase e)
  have hlen : p.eval (nodeCount t * nodeCount t) ^ 2 ≤ t ^ (2 * e) := by
    simpa only [P, Polynomial.eval_pow, Polynomial.eval_comp, Polynomial.eval_mul,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat,
      nodeCount_eq, ← sq] using hder
  have hnum : stepNumer w * 2 < t ^ 2 := by
    apply lt_of_lt_of_le (b := t)
    · dsimp [t]; omega
    · simpa using (Nat.pow_le_pow_right (n := t) (by omega) (show 1 ≤ 2 by decide))
  have hnat : p.eval (nodeCount t * nodeCount t) ^ 2 * stepNumer w * 2 < t ^ w := calc
    _ ≤ t ^ (2 * e) * stepNumer w * 2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hlen)
    _ = t ^ (2 * e) * (stepNumer w * 2) := by ring
    _ < _ := by rw [show w = 2 * e + 2 from rfl, pow_add]; gcongr
  refine ⟨t, w, by dsimp [w]; omega, by dsimp [t]; omega, ?_⟩
  rw [stepCost, ← mul_div_assoc, div_lt_div_iff₀ (by positivity) (by positivity), one_mul]
  exact_mod_cast hnat

/-- **Razborov: monotone circuits for clique need superpolynomial size.** For every polynomial
$p$ with natural-number coefficients there is a natural number $n$ with the following property.
Let $C$ be a well-formed monotone flat circuit on $n^2$ inputs, that is, every gate of $C$ is an
input variable, an and gate or an or gate, and refers only to earlier gates. Suppose that for
every bitstring $x$ of length $n^2$, when input variable $i$ is given the $i$-th bit of $x$, $C$
has a last gate with value true if and only if the $n \times n$ matrix read from $x$ in
row-major order has a clique of size $\lfloor n/3 \rfloor$, that is, a set
$S \subseteq \{0, \dots, n - 1\}$ of $\lfloor n/3 \rfloor$ vertices whose entries $(a, b)$ are
true for all distinct $a, b \in S$. Then $C$ has more than $p(n^2)$ gates.

This is a consequence of Razborov's bound `m ^ Ω(log m)` for cliques of size about `(log m) / 4` on
`m` vertices, by padding with universal vertices (A. A. Razborov, "Lower bounds on the monotone
complexity of some Boolean functions", Soviet Mathematics Doklady 31 (1985), 354-357; the bound is
restated in N. Alon and R. B. Boppana, Combinatorica 7 (1987), 1-22, Section 1, which also gives the
exponential bound). -/
theorem razborov_monotone_clique :
    ∀ p : Polynomial ℕ, ∃ n : ℕ, ∀ C : List (ACGate (n * n)),
      WellFormedCircuit C → IsMonotoneCircuit C →
        (∀ x : List Bool, x.length = n * n →
          ((circuitEval C (fun i => x.getD (i : ℕ) false)).getLast? = some true ↔
            cliqueHolds n x)) →
          C.length > p.eval (n * n) := by
  intro p
  obtain ⟨t, w, hw, ht, hp⟩ := parameters p
  refine ⟨nodeCount t, fun C hwf hm hC => ?_⟩
  by_contra! hlen
  apply (not_lt_of_ge (error_is_large ht hw C hwf hm hC)) (lt_of_le_of_lt ?_ hp)
  gcongr

end MetaMathlibExt.Complexity.KeyTheorems.RazborovMonotoneClique
