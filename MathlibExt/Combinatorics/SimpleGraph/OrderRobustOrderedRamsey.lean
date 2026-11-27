/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Order.StrictTotalOrder

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Order.Hom.PowersetCard
import MathlibExt.Combinatorics.SimpleGraph.RamseyErdosLowerBound

/-!
# Order-robust ordered Ramsey numbers of regular graphs

`AIM-COMBINATORICS-0079` (AIM Graph Ramsey theory, Ordered Ramsey
numbers, item 32): does there exist `c > 0` such that for every
sufficiently large `n` there is a 100-regular graph `H` on `n`
vertices with `r_<(H) ≥ n^(1+c)` for every ordering of `H`?

`conjecture_holds` gives an affirmative answer with `c = 1/100`. We specialize the block-coloring
argument of Balko, Jelínek and Valtr. A family of independent perfect matchings supplies enough
labeled 100-regular graphs for the counting argument.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.OrderRobustOrderedRamseyWanted

/-- **Ordered embedding.** Let $<_H$ be a strict total order on $\{0, \dots, n - 1\}$. A map
$f \colon \{0, \dots, n - 1\} \to \{0, \dots, N - 1\}$ is an ordered embedding when it is
injective and $a <_H b$ implies $f(a) < f(b)$ for all $a$ and $b$, where $\{0, \dots, N - 1\}$
carries its natural order.

Source: [AIM-COMBINATORICS-0079] Order-robust ordered Ramsey numbers of regular
graphs (aim-combinatorics-notes.json notes[78], Source item 32,
Section: Ordered Ramsey numbers, Workshop: Graph Ramsey theory,
https://www.overleaf.com/read/mnvcscjjysvg). -/
def IsOrderedEmbedding {n N : Nat} (ordH : MathlibExt.Order.StrictTotalOrder (Fin n))
    (f : Fin n → Fin N) : Prop :=
  Function.Injective f ∧ ∀ a b : Fin n, ordH.lt a b → f a < f b

/-- **Red ordered copy.** Let $H$ be a simple graph on $\{0, \dots, n - 1\}$ with a strict total
order $<_H$ on its vertices, and let $G$ be a simple graph on $\{0, \dots, N - 1\}$, the red
graph. Then $G$ contains a red ordered copy of $(H, <_H)$ when there is an ordered embedding $f$
of $(\{0, \dots, n - 1\}, <_H)$ into $\{0, \dots, N - 1\}$ such that $f(a)$ and $f(b)$ are
adjacent in $G$ whenever $a$ and $b$ are adjacent in $H$. The copy need not be induced.

Source: [AIM-COMBINATORICS-0079] Order-robust ordered Ramsey numbers of regular
graphs (aim-combinatorics-notes.json notes[78], Source item 32,
Section: Ordered Ramsey numbers, Workshop: Graph Ramsey theory,
https://www.overleaf.com/read/mnvcscjjysvg). -/
def HasRedOrderedCopy {n N : Nat} (H : SimpleGraph (Fin n))
    (ordH : MathlibExt.Order.StrictTotalOrder (Fin n)) (G : SimpleGraph (Fin N)) : Prop :=
  ∃ f : Fin n → Fin N, IsOrderedEmbedding ordH f ∧
    ∀ a b : Fin n, H.Adj a b → G.Adj (f a) (f b)

/-- **Blue ordered copy.** Let $H$ be a simple graph on $\{0, \dots, n - 1\}$ with a strict total
order $<_H$ on its vertices, and let $G$ be a simple graph on $\{0, \dots, N - 1\}$, the red
graph. Then $G$ admits a blue ordered copy of $(H, <_H)$ when there is an ordered embedding $f$
of $(\{0, \dots, n - 1\}, <_H)$ into $\{0, \dots, N - 1\}$ such that $f(a)$ and $f(b)$ are not
adjacent in $G$ whenever $a$ and $b$ are adjacent in $H$. Since $f$ is injective, these pairs are
edges of the blue graph, the complement of $G$. The copy need not be induced.

Source: [AIM-COMBINATORICS-0079] Order-robust ordered Ramsey numbers of regular
graphs (aim-combinatorics-notes.json notes[78], Source item 32,
Section: Ordered Ramsey numbers, Workshop: Graph Ramsey theory,
https://www.overleaf.com/read/mnvcscjjysvg). -/
def HasBlueOrderedCopy {n N : Nat} (H : SimpleGraph (Fin n))
    (ordH : MathlibExt.Order.StrictTotalOrder (Fin n)) (G : SimpleGraph (Fin N)) : Prop :=
  ∃ f : Fin n → Fin N, IsOrderedEmbedding ordH f ∧
    ∀ a b : Fin n, H.Adj a b → ¬ G.Adj (f a) (f b)

/-- **Ordered Ramsey property.** Let $H$ be a simple graph on $\{0, \dots, n - 1\}$ with a strict
total order $<_H$ on its vertices. A natural number $N$ has the ordered Ramsey property for
$(H, <_H)$ when every simple graph $G$ on $\{0, \dots, N - 1\}$ contains a red ordered copy of
$(H, <_H)$ or admits a blue ordered copy of $(H, <_H)$. Equivalently, every red/blue colouring of
the edges of the complete graph on $\{0, \dots, N - 1\}$ with its natural order, with red edges
those of $G$, contains a monochromatic ordered copy of $(H, <_H)$.

Source: [AIM-COMBINATORICS-0079] Order-robust ordered Ramsey numbers of regular
graphs (aim-combinatorics-notes.json notes[78], Source item 32,
Section: Ordered Ramsey numbers, Workshop: Graph Ramsey theory,
https://www.overleaf.com/read/mnvcscjjysvg). -/
def OrderedRamseyProp {n : Nat} (H : SimpleGraph (Fin n))
    (ordH : MathlibExt.Order.StrictTotalOrder (Fin n)) (N : Nat) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    HasRedOrderedCopy H ordH G ∨ HasBlueOrderedCopy H ordH G

/-- **Ordered Ramsey number.** For a simple graph $H$ on $\{0, \dots, n - 1\}$ with a strict total
order $<_H$ on its vertices, the ordered Ramsey number $r_<(H, <_H)$ is the least natural number
$N$ with the ordered Ramsey property for $(H, <_H)$, that is, such that every red/blue colouring
of the edges of the complete graph on $\{0, \dots, N - 1\}$ with its natural order contains a
monochromatic ordered copy of $(H, <_H)$. It is $0$ if no such $N$ exists.

Source: [AIM-COMBINATORICS-0079] Order-robust ordered Ramsey numbers of regular
graphs (aim-combinatorics-notes.json notes[78], Source item 32,
Section: Ordered Ramsey numbers, Workshop: Graph Ramsey theory,
https://www.overleaf.com/read/mnvcscjjysvg). -/
noncomputable def orderedRamseyNumber {n : Nat} (H : SimpleGraph (Fin n))
    (ordH : MathlibExt.Order.StrictTotalOrder (Fin n)) : Nat :=
  sInf { N : Nat | OrderedRamseyProp H ordH N }

/-- **Order-robust ordered Ramsey conjecture for 100-regular graphs.** There are a real number
$c > 0$ and a natural number $N_0$ such that for every $n \ge N_0$ there is a $100$-regular simple
graph $H$ on $\{0, \dots, n - 1\}$ such that $r_<(H, <_H) \ge n^{1+c}$ for every strict total
order $<_H$ on its vertices, where $r_<(H, <_H)$ is the ordered Ramsey number of $H$ with the
order $<_H$.

This is the AIM question asking whether such a $c$ exists, stated as a claim.

Source: [AIM-COMBINATORICS-0079] Order-robust ordered Ramsey numbers of regular
graphs (aim-combinatorics-notes.json notes[78], Source item 32,
Section: Ordered Ramsey numbers, Workshop: Graph Ramsey theory,
https://www.overleaf.com/read/mnvcscjjysvg). -/
def conjecture : Prop :=
  ∃ c : Real, 0 < c ∧ ∃ N0 : Nat, ∀ n : Nat, N0 ≤ n →
    ∃ H : SimpleGraph (Fin n), letI : H.LocallyFinite := fun _ ↦ Fintype.ofFinite _;
      H.IsRegularOfDegree 100 ∧
      ∀ ordH : MathlibExt.Order.StrictTotalOrder (Fin n),
        Real.rpow (n : Real) ((1 : Real) + c) ≤
          (orderedRamseyNumber H ordH : Real)

open SimpleGraph Function Finset

private theorem exists_rank_equiv {D : Type*} [Fintype D] {n : ℕ} (hn : Fintype.card D = n)
    (o : MathlibExt.Order.StrictTotalOrder D) :
    ∃ e : D ≃ Fin n, ∀ a b, o.lt a b → e a < e b := by
  classical
  let : LinearOrder D := linearOrderOfSTO o.lt
  let e := Fintype.orderIsoFinOfCardEq D hn
  exact ⟨e.symm.toEquiv, fun _ _ h => e.symm.strictMono h⟩

private theorem hasRedOrderedCopy_of_clique {n N : ℕ} (H : SimpleGraph (Fin n))
    (o : MathlibExt.Order.StrictTotalOrder (Fin n)) (G : SimpleGraph (Fin N))
    (h : (completeGraph (Fin n)).IsContained G) : HasRedOrderedCopy H o G := by
  classical
  obtain ⟨f⟩ := h
  obtain ⟨e, he⟩ := exists_rank_equiv (Fintype.card_fin n) o
  let s := univ.map f.toEmbedding
  have hs : s.card = n := by simp [s]
  let g := s.orderEmbOfFin hs
  refine ⟨fun a => g (e a), ⟨g.injective.comp e.injective, fun a b hab =>
    g.strictMono (he a b hab)⟩, ?_⟩
  intro a b hab
  have hcl := SimpleGraph.isNClique_map_copy_top f
  have hc : G.IsClique (s : Set (Fin N)) := hcl.isClique
  exact hc (s.orderEmbOfFin_mem hs _) (s.orderEmbOfFin_mem hs _)
    ((g.injective.comp e.injective).ne hab.ne)

private theorem exists_orderedRamseyProp {n : ℕ} (H : SimpleGraph (Fin n))
    (o : MathlibExt.Order.StrictTotalOrder (Fin n)) : ∃ N, OrderedRamseyProp H o N := by
  obtain ⟨N, hN⟩ := RamseyErdosLowerBound.exists_classicalRamsey n n
  refine ⟨N, fun G => ?_⟩
  rcases hN G with h | h
  · exact .inl (hasRedOrderedCopy_of_clique H o G h)
  · obtain ⟨f, hf, hc⟩ := hasRedOrderedCopy_of_clique H o Gᶜ h
    exact .inr ⟨f, hf, fun a b hab => (hc a b hab).2⟩

private theorem lt_orderedRamseyNumber_of_failure {n T : ℕ} {H : SimpleGraph (Fin n)}
    {o : MathlibExt.Order.StrictTotalOrder (Fin n)} (h : ¬ OrderedRamseyProp H o T) :
    T < orderedRamseyNumber H o := by
  by_contra! hle
  apply h
  let i := Fin.castLEEmb hle
  have hi : StrictMono i := fun _ _ h => h
  intro G
  have hN : OrderedRamseyProp H o (orderedRamseyNumber H o) :=
    Nat.sInf_mem (s := {k | OrderedRamseyProp H o k}) (exists_orderedRamseyProp H o)
  rcases hN (G.comap i) with ⟨f, ⟨hf, ho⟩, hc⟩ | ⟨f, ⟨hf, ho⟩, hc⟩
  · exact .inl ⟨i ∘ f, ⟨i.injective.comp hf, fun a b h => hi (ho a b h)⟩, hc⟩
  · exact .inr ⟨i ∘ f, ⟨i.injective.comp hf, fun a b h => hi (ho a b h)⟩, hc⟩

/-- Adding the index turns a weakly increasing sequence into a strictly increasing one.
Its range in `Fin (n + t)` determines the sequence. -/
private theorem card_monotone_le (n t : ℕ) :
    Nat.card {g : Fin n → Fin t // Monotone g} ≤ 2 ^ (n + t) := by
  let enc (g : {g : Fin n → Fin t // Monotone g}) : Fin n ↪o Fin (n + t) :=
    OrderEmbedding.ofStrictMono (fun i => ⟨i.val + (g.val i).val,
      Nat.add_lt_add i.isLt (g.val i).isLt⟩) fun i j h =>
        Nat.add_lt_add_of_lt_of_le h (g.prop h.le)
  have hinj : Injective enc := by
    intro g h he
    apply Subtype.ext
    funext i
    have heq := congrArg (fun (f : Fin n ↪o Fin (n + t)) => (f i).val) he
    exact Fin.ext (Nat.add_left_cancel heq)
  have h := Nat.card_le_card_of_injective _
    (Set.powersetCard.ofFinEmbEquiv.injective.comp hinj)
  refine h.trans ?_
  rw [Set.powersetCard.card, Nat.card_fin]
  exact Nat.choose_le_two_pow _ _

open MeasureTheory unitInterval
open MathlibExt.Probability.Combinatorics.RandomSubset

/-- A random two-coloring splits all the prescribed sets if the sum of their
monochromatic probabilities is less than one. -/
private theorem exists_splitting_coloring {B E : Type*} [Finite E]
    (s : Finset B) (D : B → Finset E) (M : ℕ)
    (hs : 2 * s.card < 2 ^ M) (hD : ∀ i ∈ s, M ≤ (D i).card) :
    ∃ ω : E → Bool, ∀ i ∈ s, ω ∉ containsEvent (D i) ∪ avoidEvent (D i) := by
  classical
  let := Fintype.ofFinite E
  let half : I := ⟨1 / 2, by norm_num, by norm_num⟩
  let μ := randomSubsetLaw (fun _ : E => half)
  let mono (i : B) := containsEvent (D i) ∪ avoidEvent (D i)
  have he (i) (hi : i ∈ s) : μ.real (mono i) ≤ 2 / (2 : ℝ) ^ M := calc
    _ ≤ μ.real (containsEvent (D i)) + μ.real (avoidEvent (D i)) := measureReal_union_le _ _
    _ = 2 / 2 ^ (D i).card := by
      rw [randomSubsetLaw_real_containsEvent, randomSubsetLaw_real_avoidEvent,
        prod_const, prod_const, show (half : ℝ) = 1 / 2 from rfl,
        show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, one_div, inv_pow, ← two_mul, div_eq_mul_inv]
    _ ≤ _ := by gcongr <;> first | exact hD i hi | norm_num
  let bad := ⋃ i ∈ s, mono i
  have hb : μ.real bad < 1 := calc
    _ ≤ ∑ i ∈ s, μ.real (mono i) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ s, 2 / (2 : ℝ) ^ M := sum_le_sum he
    _ < 1 := by
      rw [sum_const, nsmul_eq_mul, ← mul_div_assoc, div_lt_one (by positivity), mul_comm]
      exact_mod_cast hs
  obtain ⟨ω, hω⟩ : ∃ ω, ω ∉ bad := by
    by_contra! h
    rw [Set.eq_univ_of_forall h, probReal_univ] at hb
    exact hb.false
  exact ⟨ω, fun i hi h => hω (Set.mem_biUnion hi h)⟩

private noncomputable def occupiedPairs {n t : ℕ} (H : SimpleGraph (Fin n)) (p : Fin n → Fin t) :
    Finset (Sym2 (Fin t)) := by
  classical
  exact H.edgeFinset.image (Sym2.map p)

/-- Color pairs of host blocks independently, including each diagonal block pair.
For a fixed vertex order, every embedding induces a weakly increasing sequence of block indices.
Its occupied pairs determine whether a monochromatic copy is possible. -/
private theorem lt_orderedRamseyNumber_of_occupiedPairs {n t s M : ℕ} (H : SimpleGraph (Fin n))
    (hsize : n + t + 1 < M)
    (hH : ∀ f : Fin n ↪ Fin (t * s), M ≤ (occupiedPairs H (fun a => (f a).divNat)).card)
    (o : MathlibExt.Order.StrictTotalOrder (Fin n)) : t * s < orderedRamseyNumber H o := by
  classical
  apply lt_orderedRamseyNumber_of_failure
  obtain ⟨e, he⟩ := exists_rank_equiv (Fintype.card_fin n) o
  let B := {g : Fin n → Fin t // Monotone g}
  let D (g : B) := occupiedPairs H (fun a => g.val (e a))
  let F := univ.filter fun g : B => M ≤ (D g).card
  have hc : F.card ≤ 2 ^ (n + t) := (card_le_univ _).trans (by
    rw [← Nat.card_eq_fintype_card]; exact card_monotone_le n t)
  have hcount : 2 * F.card < 2 ^ M := calc
    _ ≤ 2 * 2 ^ (n + t) := by omega
    _ = 2 ^ (n + t + 1) := by rw [pow_succ, mul_comm]
    _ < _ := Nat.pow_lt_pow_right (by decide) hsize
  obtain ⟨ω, hω⟩ := exists_splitting_coloring F D M hcount (fun g hg => (mem_filter.mp hg).2)
  let G := fromEdgeSet {p : Sym2 (Fin (t * s)) | ω (p.map Fin.divNat) = true}
  intro hR
  obtain ⟨b, f, hf, hcol⟩ : ∃ (b : Bool) (f : Fin n → Fin (t * s)), IsOrderedEmbedding o f ∧
      ∀ a z, H.Adj a z → ω s((f a).divNat, (f z).divNat) = b := by
    rcases hR G with ⟨f, hf, h⟩ | ⟨f, hf, h⟩
    · exact ⟨true, f, hf, fun a z hG => (h a z hG).1⟩
    · refine ⟨false, f, hf, fun a z hG => ?_⟩
      apply Bool.eq_false_iff.mpr
      exact fun hh => h a z hG ⟨hh, hf.1.ne hG.ne⟩
  let g : B := ⟨fun a => (f (e.symm a)).divNat, by
    apply monotone_iff_forall_lt.mpr
    intro a z haz
    have hne : e.symm a ≠ e.symm z := e.symm.injective.ne haz.ne
    have ho : o.lt (e.symm a) (e.symm z) := (o.total hne).resolve_right (by
      intro h; have := he _ _ h; exact haz.not_gt (by simpa using this))
    exact Nat.div_le_div_right (hf.2 _ _ ho).le⟩
  have hfun : (fun a => g.val (e a)) = fun a => (f a).divNat := by simp [g]
  have hD : D g = occupiedPairs H (fun a => (f a).divNat) := congrArg (occupiedPairs H) hfun
  have hg : g ∈ F := mem_filter.mpr ⟨mem_univ _, hD ▸ hH ⟨f, hf.1⟩⟩
  have hall : ∀ p ∈ D g, ω p = b := by
    rw [hD]
    intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    induction q using Sym2.inductionOn with
    | _ a z => exact hcol a z (by simpa using hq)
  cases b with
  | false => exact hω g hg (Or.inr hall)
  | true => exact hω g hg (Or.inl hall)

private noncomputable def hostPairs {t : ℕ} (s : ℕ) (q : Sym2 (Fin t)) :
    Finset (Sym2 (Fin (t * s))) :=
  univ.image fun ij : Fin s × Fin s =>
    s(finProdFinEquiv (q.out.1, ij.1), finProdFinEquiv (q.out.2, ij.2))

private theorem mk_mem_hostPairs {t s : ℕ} (x y : Fin (t * s)) :
    s(x, y) ∈ hostPairs s s(x.divNat, y.divNat) := by
  let q := s(x.divNat, y.divNat)
  have hx : finProdFinEquiv (x.divNat, x.modNat) = x := finProdFinEquiv.apply_symm_apply x
  have hy : finProdFinEquiv (y.divNat, y.modNat) = y := finProdFinEquiv.apply_symm_apply y
  change s(x, y) ∈ hostPairs s q
  rcases Sym2.eq_iff.mp (Sym2.mk_fst_out_snd_out q) with h | h
  · exact mem_image.mpr ⟨(x.modNat, y.modNat), mem_univ _, by simp only [h.1, h.2, hx, hy]⟩
  · refine mem_image.mpr ⟨(y.modNat, x.modNat), mem_univ _, ?_⟩
    simp only [h.1, h.2, hx, hy]
    exact Sym2.eq_swap

/-- Count the graphs whose edges fit into at most `M` block pairs for some embedding.
Once the embedding and the pairs are fixed, all `k` edges come from at most `M * s²` sites. -/
private theorem exists_many_occupiedPairs {n t s k M : ℕ} (R : Finset (SimpleGraph (Fin n)))
    (hk : ∀ H ∈ R, Nat.card H.edgeSet = k) (hM : M ≤ Nat.card (Sym2 (Fin t)))
    (hcount : (t * s) ^ n * ((t * t) ^ M * (M * (s * s)).choose k) < R.card) :
    ∃ H ∈ R, ∀ f : Fin n ↪ Fin (t * s), M ≤ (occupiedPairs H (fun a => (f a).divNat)).card := by
  classical
  let B := Sym2 (Fin t)
  let A := (univ : Finset B).powersetCard M
  let C (f : Fin n ↪ Fin (t * s)) (S : Finset B) :=
    R.filter fun H => occupiedPairs H (fun a => (f a).divNat) ⊆ S
  have hc (f) (S) (hS : S ∈ A) : (C f S).card ≤ (M * (s * s)).choose k := by
    let L := S.biUnion (hostPairs s)
    let enc (H : SimpleGraph (Fin n)) := H.edgeFinset.map f.sym2Map
    have hi : (C f S).card ≤ (L.powersetCard k).card := by
      apply card_le_card_of_injOn enc
      · intro H hH
        obtain ⟨hR, hsub⟩ := mem_filter.mp hH
        apply mem_powersetCard.mpr
        refine ⟨?_, by simpa [enc, edgeFinset_card, ← Nat.card_eq_fintype_card] using hk H hR⟩
        intro z hz
        obtain ⟨q, hq, rfl⟩ := mem_map.mp hz
        induction q using Sym2.inductionOn with
        | _ x y =>
          refine mem_biUnion.mpr ⟨_, hsub (mem_image_of_mem _ hq), ?_⟩
          exact mk_mem_hostPairs (f x) (f y)
      · intro H _ J _ he
        exact edgeFinset_inj.mp (map_injective f.sym2Map he)
    have hL : L.card ≤ M * (s * s) := by
      rw [← (mem_powersetCard.mp hS).2]
      apply card_biUnion_le_card_mul
      intro q _
      exact card_image_le.trans (by simp)
    exact hi.trans ((card_powersetCard ..) ▸ Nat.choose_le_choose k hL)
  by_contra! h
  have hsub : R ⊆ univ.biUnion (fun f => A.biUnion (C f)) := by
    intro H hR
    obtain ⟨f, hf⟩ := h H hR
    obtain ⟨S, hS, hSu, hS'⟩ := exists_subsuperset_card_eq (subset_univ _) hf.le
      (by simpa [Nat.card_eq_fintype_card] using hM : M ≤ (univ : Finset B).card)
    exact mem_biUnion.mpr ⟨f, mem_univ _, mem_biUnion.mpr
      ⟨S, mem_powersetCard.mpr ⟨hSu, hS'⟩, mem_filter.mpr ⟨hR, hS⟩⟩⟩
  have hB : Fintype.card B ≤ t * t := by
    simpa using Fintype.card_le_of_surjective _ (@Sym2.mk_surjective (Fin t))
  have hA : A.card ≤ (t * t) ^ M := calc
    _ = (Fintype.card B).choose M := by simp [A]
    _ ≤ (Fintype.card B) ^ M := Nat.choose_le_pow _ _
    _ ≤ _ := Nat.pow_le_pow_left hB M
  have hF : (univ : Finset (Fin n ↪ Fin (t * s))).card ≤ (t * s) ^ n := by
    simpa using Fintype.card_le_of_injective _ (@DFunLike.coe_injective (Fin n ↪ Fin (t * s))
      (Fin n) (fun _ => Fin (t * s)) _)
  apply hcount.not_ge
  refine (card_le_card hsub).trans ((card_biUnion_le_card_mul _ _ _ ?_).trans
    (Nat.mul_le_mul_right _ hF))
  exact fun f _ => (card_biUnion_le_card_mul _ _ _ (hc f)).trans (Nat.mul_le_mul_right _ hA)

private abbrev Vertex (m r : ℕ) :=
  (Fin 100 × Fin m) ⊕ (Fin 100 × Fin m) ⊕ (Fin r × Fin 101)

private abbrev Matchings (m : ℕ) := Fin 100 → Fin 100 → Equiv.Perm (Fin m)

/-- Between each left and right part put a perfect matching. Fill the remaining vertices with
copies of the complete graph on 101 vertices. -/
private def liftGraph {m : ℕ} (r : ℕ) (π : Matchings m) : SimpleGraph (Vertex m r) where
  Adj
    | .inl (i, x), .inr (.inl (j, y)) | .inr (.inl (j, y)), .inl (i, x) => π i j x = y
    | .inr (.inr (a, x)), .inr (.inr (b, y)) => a = b ∧ x ≠ y
    | _, _ => False
  symm.symm := by
    rintro (⟨i, x⟩ | ⟨j, y⟩ | ⟨k, z⟩) (⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩) <;> simp_all [eq_comm]
  loopless.irrefl := by rintro (⟨i, x⟩ | ⟨j, y⟩ | ⟨k, z⟩) <;> simp

private theorem liftGraph_injective {m r : ℕ} : Injective (liftGraph (m := m) r) := by
  intro π τ h
  funext i j
  apply Equiv.ext
  intro x
  have hAdj : (liftGraph r τ).Adj (.inl (i, x)) (.inr (.inl (j, π i j x))) := by rw [← h]; rfl
  exact Eq.symm hAdj

private theorem liftGraph_ncard_neighborSet {m r : ℕ} (π : Matchings m) (x : Vertex m r) :
    ((liftGraph r π).neighborSet x).ncard = 100 := by
  classical
  let G := liftGraph r π
  change (G.neighborSet x).ncard = 100
  rw [G.ncard_neighborSet]
  change (G.neighborFinset x).card = 100
  rcases x with ⟨i, x⟩ | ⟨j, y⟩ | ⟨k, z⟩
  · let f (j : Fin 100) : Vertex m r := .inr (.inl (j, π i j x))
    have hf : Injective f := fun _ _ h => (Prod.mk.inj (Sum.inl.inj (Sum.inr.inj h))).1
    have he : G.neighborFinset (.inl (i, x)) = univ.image f := by
      ext (⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩) <;> rw [mem_neighborFinset] <;>
        simp [G, liftGraph, f, eq_comm]
    rw [he, card_image_of_injective _ hf]; simp
  · let f (i : Fin 100) : Vertex m r := .inl (i, (π i j).symm y)
    have hf : Injective f := fun _ _ h => (Prod.mk.inj (Sum.inl.inj h)).1
    have he : G.neighborFinset (.inr (.inl (j, y))) = univ.image f := by
      ext (⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩) <;> rw [mem_neighborFinset] <;>
        simp [G, liftGraph, f, Equiv.eq_symm_apply, eq_comm]
    rw [he, card_image_of_injective _ hf]; simp
  · let f (w : Fin 101) : Vertex m r := .inr (.inr (k, w))
    have hf : Injective f := fun _ _ h => (Prod.mk.inj (Sum.inr.inj (Sum.inr.inj h))).2
    have he : G.neighborFinset (.inr (.inr (k, z))) = (univ.erase z).image f := by
      ext (⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩) <;> rw [mem_neighborFinset] <;>
        simp [G, liftGraph, f, eq_comm, and_comm]
    rw [he, card_image_of_injective _ hf, card_erase_of_mem (mem_univ _)]; simp

/-- Each of the 100 × 100 matchings can be recovered from the labeled graph, so choosing
their permutations independently gives `(m!) ^ 10000` distinct 100-regular graphs. -/
private theorem exists_regular_family {n m r : ℕ} (hn : n = 200 * m + 101 * r) :
    ∃ R : Finset (SimpleGraph (Fin n)), R.card = m.factorial ^ 10000 ∧
      ∀ H ∈ R, ∀ v, (H.neighborSet v).ncard = 100 := by
  classical
  let e := Fintype.equivFinOfCardEq (α := Vertex m r) (by simp [Vertex, hn]; omega : _ = n)
  let f (π : Matchings m) := (liftGraph r π).map e.toEmbedding
  have hf : Injective f := (SimpleGraph.map_injective e.toEmbedding).comp liftGraph_injective
  refine ⟨univ.image f, ?_, ?_⟩
  · rw [card_image_of_injective _ hf]
    simp [Matchings, Fintype.card_perm, ← pow_mul]
  · intro H hH v
    obtain ⟨π, _, rfl⟩ := mem_image.mp hH
    obtain ⟨x, rfl⟩ := e.surjective v
    exact (Set.ncard_congr' ((Iso.map e (liftGraph r π)).mapNeighborSet x)).symm.trans
      (liftGraph_ncard_neighborSet π x)

private theorem choose_le_block_pow {n s : ℕ} (hn : 0 < n) :
    (3 * n * (s * s)).choose (50 * n) ≤ (s * s) ^ (50 * n) := by
  by_cases h : 50 * n ≤ 3 * n * (s * s)
  · have hterm := Finset.single_le_sum (f := fun i => ((3 * n * (s * s)).choose i : ℝ))
      (fun _ _ => Nat.cast_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_self (50 * n)))
    have hbase : Real.exp 1 / (50 * n) * (3 * n * (s * s)) ≤ (s * s : ℝ) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le
        (show 0 ≤ (3 * n * (s * s) : ℝ) by positivity)]
    have hreal := hterm.trans (Real.sum_choose_le_exp_pow h)
    push_cast at hreal
    exact_mod_cast hreal.trans (pow_le_pow_left₀ (by positivity) hbase _)
  · simp [Nat.choose_eq_zero_of_lt (lt_of_not_ge h)]

/-- Bound the number of graphs with a sparse block partition by `n ^ (10 * n)`.
The last factors of `m!` already give `n ^ (m / 4) ≤ m!`. -/
private theorem count_lt_factorial_pow {n m s : ℕ} (hn : 1 < n) (hu : n ≤ 900 * (m / 4))
    (hu' : 900 ≤ m / 4) (hs : s ≤ n) (hs' : s ^ 100 ≤ n ^ 2) :
    (n * s) ^ n * ((n * n) ^ (3 * n) * (3 * n * (s * s)).choose (50 * n)) <
      m.factorial ^ 10000 := by
  let u := m / 4
  have hsmall :
      (n * s) ^ n * ((n * n) ^ (3 * n) * (3 * n * (s * s)).choose (50 * n)) ≤
        n ^ (10 * n) := calc
    _ ≤ (n * n) ^ n * ((n * n) ^ (3 * n) * (s * s) ^ (50 * n)) := by
      gcongr; exact choose_le_block_pow (by omega)
    _ = n ^ (2 * n) * (n ^ (6 * n) * (s ^ 100) ^ n) := by
      simp only [← sq, ← pow_mul]; ring_nf
    _ ≤ n ^ (2 * n) * (n ^ (6 * n) * (n ^ 2) ^ n) := by gcongr
    _ = _ := by rw [← pow_mul, ← pow_add, ← pow_add]; ring_nf
  have hnu : n ≤ u ^ 2 := by
    calc n ≤ 900 * u := hu
         _ ≤ u * u := Nat.mul_le_mul_right u hu'
         _ = _ := (sq _).symm
  have hf : n ^ u ≤ m.factorial := calc
    n ^ u ≤ (u ^ 2) ^ u := Nat.pow_le_pow_left hnu _
    _ = u ^ (2 * u) := (pow_mul ..).symm
    _ ≤ u ^ (m - u) := Nat.pow_le_pow_right (by dsimp [u]; omega) (by dsimp [u]; omega)
    _ ≤ u.factorial * u ^ (m - u) := Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
    _ ≤ m.factorial := Nat.factorial_mul_pow_sub_le_factorial (Nat.div_le_self ..)
  have hgap : 10 * n < u * 10000 := by change n ≤ 900 * u at hu; omega
  have hlt := Nat.pow_lt_pow_right hn hgap
  rw [pow_mul n u 10000] at hlt
  have hpow (d : ℕ) : (n ^ u) ^ d ≤ m.factorial ^ d := Nat.pow_le_pow_left hf d
  exact hsmall.trans_lt (hlt.trans_le (hpow 10000))

/--
**The order-robust ordered Ramsey conjecture holds.** There are a real number $c > 0$ and a
natural number $N_0$ such that for every $n \ge N_0$ there is a $100$-regular simple graph $H$ on
$\{0, \dots, n - 1\}$ such that $r_<(H, <_H) \ge n^{1+c}$ for every strict total order $<_H$ on
its vertices. Here $r_<(H, <_H)$ is the least $N$ such that every red/blue colouring of the edges
of the complete graph on $\{0, \dots, N - 1\}$ with its natural order contains a monochromatic
copy of $H$ (not necessarily induced) under an injective map sending $<_H$ into the natural
order, and $0$ if there is no such $N$.

Balko, Jelínek and Valtr prove that for every $d \ge 3$ almost every $d$-regular $n$-vertex
graph has ordered Ramsey number at least $n^{3/2-1/d}/(4 \log n \log \log n)$ under every vertex
ordering; for $d = 100$ this exceeds $n^{1+c}$ for any $c < 49/100$ and all large $n$.

Source: M.
Balko, V. Jelínek and P. Valtr, On ordered Ramsey numbers of bounded-degree graphs,
arXiv:1606.05628, https://arxiv.org/abs/1606.05628. Moved from
`OpenConjectures/Combinatorics/OrderRobustOrderedRamsey`.
-/
public theorem conjecture_holds : conjecture := by
  classical
  refine ⟨1 / 100, by norm_num, 2 ^ 100, ?_⟩
  intro n hn
  have hlarge : 100000000 ≤ n := le_trans (by norm_num) hn
  -- Since 101² = 51 · 200 + 1, the clique components can absorb any residue modulo 200.
  let m := n / 200 - 51 * (n % 200)
  let r := 101 * (n % 200)
  have hnm : n = 200 * m + 101 * r := by dsimp [m, r]; omega
  have hu : n ≤ 900 * (m / 4) := by dsimp [m]; omega
  have hu' : 900 ≤ m / 4 := by omega
  obtain ⟨R, hR, hreg⟩ := exists_regular_family hnm
  let x := (n : ℝ) ^ (1 / 100 : ℝ)
  let s := ⌈x⌉₊
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hx : 1 ≤ x := Real.one_le_rpow hn' (by norm_num)
  have hxpow : x ^ 100 = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ n)]
    norm_num
  have hs : s ≤ n := by
    apply Nat.ceil_le.mpr
    exact (Real.rpow_le_rpow_of_exponent_le hn' (by norm_num : (1 / 100 : ℝ) ≤ 1)).trans_eq
      (Real.rpow_one _)
  have hs' : s ^ 100 ≤ n ^ 2 := by
    have h2 : (s : ℝ) ≤ 2 * x := by
      have := Nat.ceil_lt_add_one (by linarith : 0 ≤ x)
      dsimp [s]; linarith
    have H : (s : ℝ) ^ 100 ≤ (n : ℝ) ^ 2 := calc
      _ ≤ (2 * x) ^ 100 := pow_le_pow_left₀ (by positivity) h2 _
      _ = 2 ^ 100 * n := by rw [mul_pow, hxpow]
      _ ≤ (n : ℝ) * n := by gcongr; exact_mod_cast hn
      _ = _ := (sq _).symm
    exact_mod_cast H
  have hcard (H) (h : H ∈ R) : Nat.card H.edgeSet = 50 * n := by
    have hdeg (v) : H.degree v = 100 := (H.ncard_neighborSet v).symm.trans (hreg H h v)
    have hsum := H.sum_degrees_eq_twice_card_edges
    simp only [hdeg, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    rw [Nat.card_eq_fintype_card, ← H.edgeFinset_card]
    change n * 100 = 2 * H.edgeFinset.card at hsum
    omega
  have hM : 3 * n ≤ Nat.card (Sym2 (Fin n)) := by
    rw [Nat.card_eq_fintype_card, Sym2.card, Fintype.card_fin, Nat.choose_two_right]
    have h5 : 6 ≤ n + 1 := by omega
    have hmul := Nat.mul_le_mul_right n h5
    simp only [Nat.add_sub_cancel]
    omega
  obtain ⟨H, hH, hOcc⟩ := exists_many_occupiedPairs (s := s) R hcard hM
    (hR ▸ count_lt_factorial_pow (by omega) hu hu' hs hs')
  refine ⟨H, ?_, ?_⟩
  · intro v
    exact (@ncard_neighborSet _ H v (Fintype.ofFinite _)).symm.trans (hreg H hH v)
  · intro o
    have hl := lt_orderedRamseyNumber_of_occupiedPairs H (by omega) hOcc o
    calc
      _ = (n : ℝ) * x := by
        change (n : ℝ) ^ (1 + 1 / 100 : ℝ) = _
        rw [Real.rpow_add (by positivity : (0 : ℝ) < n), Real.rpow_one]
      _ ≤ (n : ℝ) * s := by gcongr; exact Nat.le_ceil x
      _ ≤ _ := by exact_mod_cast hl.le

end MathlibExt.Combinatorics.OrderRobustOrderedRamseyWanted
