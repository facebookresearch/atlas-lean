/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.List
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Colorings of the complete `r`-uniform hypergraph (Erdős Problem 780)

Erdős Problem 780: suppose `n ≥ k r + (t - 1)(k - 1)` and the edges of the complete `r`-uniform
hypergraph on `n` vertices are colored with `t` colors. Prove that some color class contains `k`
pairwise disjoint edges.

Source: T. F. Bloom, Erdős Problems, Problem #780, https://www.erdosproblems.com/780 (status
PROVED). UnsolvedMath record UM-30007030 (`EP-780`), dataset ulamai/UnsolvedMath v1.8.0.

A coloring is any `c : Finset (Fin n) → Fin t` (only its values on `r`-subsets matter). The
statement assumes `r ≥ 1` and `t ≥ 1`: for `r = 0` the empty set is the only edge and is disjoint
from itself, and `t = 0` admits no coloring of a nonempty hypergraph. `MathlibExt` proves the Kneser
graph case `k = 2` (Lovász, `MathlibExt.Combinatorics.SimpleGraph.KneserLovasz`).
Compared with the formal-conjectures statement `ErdosProblems/780.lean` (equivalent; no code
imported).

This module proves `kneserHypergraphColoring_holds` by a cyclic-group labeling argument for
prime matching sizes and a multiplication argument for composite sizes. The proof of the
labeling obstruction uses the alternating trace on the simplices of a join, following
G. M. Ziegler, *Generalized Kneser coloring theorems with combinatorial proofs*.
https://arxiv.org/abs/math/0103146.
-/

namespace MathlibExt.Combinatorics.KneserHypergraphColoringErdosProblem780Wanted

@[expose] public section

/-- **Erdős's Kneser hypergraph problem.** The statement that for all natural numbers
$n, k, r, t$ with $r \ge 1$, $t \ge 1$ and $n \ge kr + (t - 1)(k - 1)$, every coloring of the
$r$-element subsets of $\{0, \dots, n - 1\}$ with $t$ colors has a color class containing $k$
pairwise disjoint $r$-element subsets. -/
def kneserHypergraphColoring : Prop :=
  ∀ n k r t : ℕ, 1 ≤ r → 1 ≤ t → k * r + (t - 1) * (k - 1) ≤ n →
    ∀ c : Finset (Fin n) → Fin t, ∃ (i : Fin t) (E : Finset (Finset (Fin n))),
      E ⊆ (Finset.univ : Finset (Fin n)).powersetCard r ∧ E.card = k ∧ (∀ e ∈ E, c e = i) ∧
        (E : Set (Finset (Fin n))).PairwiseDisjoint id

end

open Finset
open scoped Function
variable {V W R : Type} [CommRing R]

/-! ## Cochains on ordered simplices

The alternating face sum is expressed by recursion on the first vertex. Pulling a cochain back
along a subdivision labels the top face, then sums with signs over its codimension-one faces.
This gives a cochain map even when adjacent faces receive the same label.
-/

private def cob (f : List V → R) : List V → R
  | [] => 0
  | a :: s => f s - cob (f ∘ List.cons a) s

private lemma cob_zero (s : List V) : cob (fun _ => (0 : R)) s = 0 := by
  induction s with
  | nil => rfl
  | cons a s ih => exact (congrArg (0 - ·) ih).trans (sub_self _)

private lemma cob_sub (f g : List V → R) (s : List V) :
    cob (f - g) s = cob f s - cob g s := by
  induction s generalizing f g with
  | nil => simp [cob]
  | cons a s ih =>
    change f s - g s - cob ((f ∘ List.cons a) - (g ∘ List.cons a)) s = _
    rw [ih]
    simp only [cob]
    abel

private lemma cob_sq (f : List V → R) (s : List V) : cob (cob f) s = 0 := by
  induction s generalizing f with
  | nil => rfl
  | cons a s ih =>
    change cob f s - cob (f - cob (f ∘ List.cons a)) s = 0
    rw [cob_sub, ih]
    abel

private lemma cob_congr {f g : List V → R} {s : List V}
    (h : ∀ u, u.Sublist s → u.length + 1 = s.length → f u = g u) : cob f s = cob g s := by
  induction s generalizing f g with
  | nil => rfl
  | cons a s ih =>
    simp only [cob, h s (List.Sublist.cons _ (List.Sublist.refl _)) rfl]
    congr 1
    apply ih
    intro u hu hn
    exact h _ (hu.cons_cons _) (by simp [hn])

private lemma cob_map (e : V → W) (f : List W → R) (s : List V) :
    cob f (s.map e) = cob (f ∘ List.map e) s := by
  induction s generalizing f with
  | nil => rfl
  | cons a s ih =>
    simp only [List.map_cons, cob, Function.comp_apply, ih]
    rfl

private def pull (L : List V → W) : ℕ → (List W → R) → List V → R
  | 0, f, _ => f []
  | n + 1, f, s => cob (pull L n (f ∘ List.cons (L s))) s

private lemma pull_sub (L : List V → W) (n : ℕ) (f g : List W → R) (s : List V) :
    pull L n (f - g) s = pull L n f s - pull L n g s := by
  induction n generalizing f g s with
  | zero => rfl
  | succ n ih =>
    simp only [pull, ← cob_sub]
    apply cob_congr
    intro u _ _
    exact ih (f ∘ _) (g ∘ _) u

private lemma pull_cob (L : List V → W) (n : ℕ) (f : List W → R) (s : List V) :
    pull L (n + 1) (cob f) s = cob (pull L n f) s := by
  induction n generalizing f s with
  | zero => simp [pull, cob]
  | succ n ih =>
    change cob (pull L (n + 1) (f - cob (f ∘ List.cons (L s)))) s = _
    have h : pull L (n + 1) (f - cob (f ∘ List.cons (L s))) =
        pull L (n + 1) f - cob (pull L n (f ∘ List.cons (L s))) := by
      funext u
      rw [pull_sub, ih]; rfl
    rw [h, cob_sub, cob_sq, sub_zero]

private def pullback (L : List V → W) (f : List W → R) (s : List V) := pull L s.length f s

private lemma pullback_cob (L : List V → W) (f : List W → R) (s : List V) :
    pullback L (cob f) s = cob (pullback L f) s := by
  cases s with
  | nil => rfl
  | cons a s =>
    rw [pullback, List.length_cons, pull_cob]
    apply cob_congr
    intro u _ h
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [pullback, h]


private lemma cob_lin {I : Type} (T : Finset I) (c : I → R) (f : I → List V → R) (s : List V) :
    cob (fun q => ∑ i ∈ T, c i * f i q) s = ∑ i ∈ T, c i * cob (f i) s := by
  induction s generalizing f with
  | nil => simp [cob]
  | cons a s ih =>
    change _ - cob (fun q => ∑ i ∈ T, c i * f i (a :: q)) s = _
    rw [ih (fun i u => f i (a :: u))]
    simp [cob, mul_sub, sum_sub_distrib, Function.comp_def]

private lemma pull_lin {I : Type} (T : Finset I) (c : I → R) (f : I → List W → R)
    (L : List V → W) (n : ℕ) (s : List V) :
    pull L n (fun q => ∑ i ∈ T, c i * f i q) s = ∑ i ∈ T, c i * pull L n (f i) s := by
  induction n generalizing f s with
  | zero => rfl
  | succ n ih =>
    simp only [pull, ← cob_lin]
    apply cob_congr
    intro u _ _
    exact ih (fun i => f i ∘ List.cons (L s)) u

/-- The labels along a saturated flag of faces, starting with the largest. -/
private inductive FlagImage (L : List V → W) : List V → List W → Prop
  | nil : FlagImage L [] []
  | cons {s u w} (h : u.Sublist s) (hn : u.length + 1 = s.length) (hw : FlagImage L u w) :
      FlagImage L s (L s :: w)

private lemma pullback_congr (L : List V → W) {s : List V} {f g : List W → R}
    (h : ∀ w, FlagImage L s w → f w = g w) : pullback L f s = pullback L g s := by
  generalize hn : s.length = n
  induction n generalizing s f g with
  | zero =>
    obtain rfl := List.length_eq_zero_iff.mp hn
    exact h [] .nil
  | succ n ih =>
    simp only [pullback, hn, pull]
    apply cob_congr
    intro u hu hlen
    have un : u.length = n := by omega
    exact un ▸ ih (s := u) (f := f ∘ List.cons (L s)) (g := g ∘ List.cons (L s))
      (fun w hw => h _ (.cons hu hlen hw)) un

/-- Labels with the same rank may coincide along a flag. -/
private def RankGE (r : V → ℕ) (a b : V) := r b < r a ∨ a = b

private def Descending (r : V → ℕ) (s : List V) := s.Pairwise (fun a b => r b < r a)

private lemma weak_or_repeat {r : V → ℕ} {s : List V} (h : s.Pairwise (RankGE r)) :
    Descending r s ∨ ∃ a l u, s = l ++ a :: a :: u := by
  induction s with
  | nil => exact Or.inl .nil
  | cons a s ih =>
    obtain ⟨ha, hs⟩ := List.pairwise_cons.mp h
    rcases ih hs with hstrict | ⟨b, l, u, rfl⟩
    · cases s with
      | nil => exact Or.inl (by simp [Descending])
      | cons b s =>
        rcases ha b (.head _) with hlt | rfl
        · left
          refine List.pairwise_cons.mpr ⟨?_, hstrict⟩
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hlt
          · exact lt_trans ((List.pairwise_cons.mp hstrict).1 _ hx) hlt
        · exact Or.inr ⟨a, [], s, rfl⟩
    · exact Or.inr ⟨b, a :: l, u, rfl⟩

private def Normal (f : List V → R) := ∀ l a s, f (l ++ a :: a :: s) = 0

private lemma normal_cob {f : List V → R} (hf : Normal f) : Normal (cob f) := by
  intro l
  induction l generalizing f with
  | nil =>
    intro a s
    simp only [List.nil_append, cob, Function.comp_apply]
    have e : (f ∘ List.cons a ∘ List.cons a) = fun _ => 0 := by
      funext u
      exact hf [] a u
    rw [show (f ∘ List.cons a) ∘ List.cons a = fun _ => 0 from e, cob_zero]
    abel
  | cons b l ih =>
    intro a s
    rw [List.cons_append, cob, hf, ih (f := f ∘ List.cons b) (fun l => hf (b :: l))]
    simp

private def basis [DecidableEq V] (s w : List V) : R := if s = w then 1 else 0

private lemma normal_basis [DecidableEq V] {r : V → ℕ} {s : List V} (hs : Descending r s) :
    Normal (basis s : List V → R) := by
  intro l a u
  apply ite_eq_right
  rintro rfl
  have nodup : (l ++ a :: a :: u).Nodup := hs.imp (fun h e => by subst_vars; exact lt_irrefl _ h)
  exact (List.nodup_cons.mp (List.nodup_append'.mp nodup).2.1).1 (.head _)


private lemma eval_basis [DecidableEq V] (K : Finset (List V)) (f : List V → R) (w : List V) :
    ∑ u ∈ K, f u * basis u w = if w ∈ K then f w else 0 := by
  classical
  simp [basis, mul_ite]

/-! ## The trace obstruction

Coning a simplex to an extra vertex gives a homotopy. On the diagonal its two boundary terms
have opposite signs in consecutive dimensions, so the alternating trace vanishes. Repeated
vertices contribute zero because the basis cochains and their coboundaries are normalized.
-/

private lemma trace_zero [DecidableEq V] (r : V → ℕ) (K : Finset (List V)) (v : V)
    (L : List V → V) (down : ∀ s ∈ K, ∀ u, u.Sublist s → u ∈ K)
    (strict : ∀ s ∈ K, Descending r s)
    (flags : ∀ s ∈ K, ∀ w, FlagImage L (v :: s) w →
      w ∈ K ∨ ∃ a l u, w = l ++ a :: a :: u) :
    ∑ s ∈ K, (-1 : R) ^ s.length * pullback L (basis s) s = 0 := by
  classical
  -- Boundary coefficients and coefficients of the cone homotopy.
  let D (q s : List V) : R := cob (basis q) s
  let H (s q : List V) : R := pullback L (basis q) (v :: s)
  have d1 (q s : List V) (hs : s ∈ K) (hq : q ∈ K) :
      pullback L (cob (basis q : List V → R)) (v :: s) = ∑ t ∈ K, D q t * H s t := by
    change _ = ∑ t ∈ K, D q t * pull L (v :: s).length (basis t) (v :: s)
    rw [← pull_lin]
    apply pullback_congr
    intro w hw
    rw [eval_basis]
    split_ifs with h
    · rfl
    · obtain ⟨a, l, u, rfl⟩ := (flags s hs w hw).resolve_left h
      exact normal_cob (normal_basis (strict q hq)) l a u
  have d2 (s q : List V) (hs : s ∈ K) :
      cob (fun u => H u q) s = ∑ t ∈ K, H t q * D t s := by
    change cob _ s = ∑ t ∈ K, H t q * cob (basis t) s
    rw [← cob_lin]
    apply cob_congr
    intro u hu _
    simp [eval_basis, down s hs u hu]
  have diag (s : List V) (hs : s ∈ K) :
      pullback L (basis s : List V → R) s = (∑ t ∈ K, D s t * H s t) + ∑ t ∈ K, H t s * D t s := by
    rw [← d1 s s hs hs, ← d2 s s hs, pullback_cob]
    exact (sub_add_cancel _ _).symm
  have sign (s t : List V) : (-1 : R) ^ s.length * D s t = -((-1) ^ t.length * D s t) := by
    by_cases h : s.length + 1 = t.length
    · rw [← h, pow_succ]
      ring
    · have hd : D s t = 0 := by
        rw [← cob_zero t]
        apply cob_congr
        intro u _ hu
        apply ite_eq_right
        rintro rfl
        exact h hu
      simp [hd]
  simp_rw [sum_congr rfl (fun s hs => congrArg ((-1 : R) ^ s.length * ·) (diag s hs)),
    mul_add, mul_sum, sum_add_distrib]
  rw [sum_comm (s := K) (t := K) (f := fun s t => (-1 : R) ^ s.length * (H t s * D t s))]
  apply add_eq_zero_iff_eq_neg.mpr
  simp only [← sum_neg_distrib]
  refine sum_congr rfl (fun s _ => sum_congr rfl (fun t _ => ?_))
  calc
    _ = ((-1 : R) ^ s.length * D s t) * H s t := by ring
    _ = _ := by rw [sign]; ring


private lemma pullback_map (L : List V → W) (e : V → V) (g : W → W)
    (f : List W → R) (s : List V)
    (h : ∀ u, u.Sublist s → u ≠ [] → L (u.map e) = g (L u)) :
    pullback L f (s.map e) = pullback L (f ∘ List.map g) s := by
  suffices aux : ∀ n (s : List V) (f : List W → R), s.length = n →
      (∀ u, u.Sublist s → u ≠ [] → L (u.map e) = g (L u)) →
      pull L n f (s.map e) = pull L n (f ∘ List.map g) s by
    simpa [pullback] using aux s.length s f rfl h
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro s f hn h
    have ne : s ≠ [] := by rintro rfl; simp at hn
    simp only [pull, cob_map, h s (.refl _) ne]
    apply cob_congr
    intro u hu hun
    exact ih u (f ∘ List.cons (g (L s))) (by omega)
      (fun t ht => h t (ht.trans hu))

private lemma flags_ordered (r : V → ℕ) (L : List V → V) (m : ℕ)
    (bound : ∀ s, Descending r s → s ≠ [] → r (L s) < m)
    (mono : ∀ s, Descending r s → ∀ u, u.Sublist s → u ≠ [] → RankGE r (L s) (L u))
    {s w : List V} (hw : FlagImage L s w) (hs : Descending r s) :
    w.Pairwise (RankGE r) ∧ ∀ b ∈ w, r b < m ∧ ∃ u, u.Sublist s ∧ u ≠ [] ∧ L u = b := by
  induction hw with
  | nil => simp
  | @cons s u w hu hn hw ih =>
    obtain ⟨ord, members⟩ := ih (hs.sublist hu)
    have ne : s ≠ [] := by rintro rfl; simp at hn
    refine ⟨List.pairwise_cons.mpr ⟨?_, ord⟩, ?_⟩
    · intro b hb
      obtain ⟨-, t, ht, hne, rfl⟩ := members b hb
      exact mono s hs t (ht.trans hu) hne
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨bound _ hs ne, s, .refl _, ne, rfl⟩
      · obtain ⟨lt, t, ht, hne, rfl⟩ := members b hb
        exact ⟨lt, t, ht.trans hu, hne, rfl⟩

private noncomputable def faces [Fintype V] (r : V → ℕ) (m : ℕ) : Finset (List V) := by
  classical
  exact (univ.image (Subtype.val : {l : List V // l.Nodup} → List V)).filter
    (fun s => Descending r s ∧ ∀ b ∈ s, r b < m)

private lemma mem_faces [Fintype V] {r : V → ℕ} {m : ℕ} {s : List V} :
    s ∈ faces r m ↔ Descending r s ∧ ∀ b ∈ s, r b < m := by
  classical
  simp only [faces, mem_filter, mem_image, mem_univ, true_and, Subtype.exists, exists_prop]
  constructor
  · exact And.right
  · intro h
    exact ⟨⟨s, h.1.imp (fun ht e => by subst_vars; exact lt_irrefl _ ht), rfl⟩, h⟩

private abbrev Vertex (m p : ℕ) := Fin (m + 1) × ZMod p

private def level {m p : ℕ} (a : Vertex m p) : ℕ := a.1.val

private def shift {m p : ℕ} (g : ZMod p) (a : Vertex m p) : Vertex m p := (a.1, g + a.2)

private lemma shift_inj {m p : ℕ} (g : ZMod p) : Function.Injective (shift (m := m) g) := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  simpa [shift] using h

private lemma faces_map {m p : ℕ} [NeZero p] (g : ZMod p) (s : List (Vertex m p)) :
    s.map (shift g) ∈ faces level m ↔ s ∈ faces level m := by
  simp only [mem_faces, Descending, List.pairwise_map, List.forall_mem_map]
  rfl


/-- An equivariant labeling of the join of `m + 1` copies of the cyclic group cannot have
only `m` ranks, with labels weakly decreasing along flags. Translation groups the nonempty
simplices of each rank into orbits of size `p`, leaving the empty simplex with coefficient one. -/
private theorem no_label {m p : ℕ} [Fact p.Prime] (L : List (Vertex m p) → Vertex m p)
    (bound : ∀ s, Descending level s → s ≠ [] → level (L s) < m)
    (mono : ∀ s, Descending level s → ∀ u, u.Sublist s → u ≠ [] → RankGE level (L s) (L u))
    (equiv : ∀ s, Descending level s → s ≠ [] → ∀ g, L (s.map (shift g)) = shift g (L s)) :
    False := by
  classical
  let K := faces (level (m := m) (p := p)) m
  let v : Vertex m p := (Fin.last m, 0)
  let F (s : List (Vertex m p)) : ZMod p := (-1) ^ s.length * pullback L (basis s) s
  have zero : ∑ s ∈ K, F s = 0 := by
    apply trace_zero level K v L
    · intro s hs u hu
      obtain ⟨hs, hm⟩ := mem_faces.mp hs
      exact mem_faces.mpr ⟨hs.sublist hu, fun b hb => hm b (hu.subset hb)⟩
    · exact fun s hs => (mem_faces.mp hs).1
    · intro s hs w hw
      obtain ⟨hs, hm⟩ := mem_faces.mp hs
      have sv : Descending level (v :: s) := List.pairwise_cons.mpr ⟨hm, hs⟩
      obtain ⟨ord, members⟩ := flags_ordered level L m bound mono hw sv
      rcases weak_or_repeat ord with ht | h
      · exact Or.inl (mem_faces.mpr ⟨ht, fun b hb => (members b hb).1⟩)
      · exact Or.inr h
  have inv (s : List (Vertex m p)) (hs : s ∈ K) (g : ZMod p) : F (s.map (shift g)) = F s := by
    dsimp only [F]
    rw [List.length_map, pullback_map L (shift g) (shift g)]
    · congr 2
      funext t
      simp [basis, (List.map_injective_iff.mpr (shift_inj g)).eq_iff]
    · exact fun u hu hne => equiv u ((mem_faces.mp hs).1.sublist hu) hne g
  let K' := K.erase []
  let phase (s : List (Vertex m p)) := (s.head?.map Prod.snd).getD 0
  have phase_shift (s : List (Vertex m p)) (hne : s ≠ []) (g : ZMod p) :
      phase (s.map (shift g)) = g + phase s := by
    cases s with
    | nil => contradiction
    | cons a s => rfl
  have aff (s : List (Vertex m p)) (g : ZMod p) :
      s.map (shift g) ∈ K' ↔ s ∈ K' := by
    simp [K', K, faces_map]
  let fiber (g : ZMod p) := K'.filter (fun s => phase s = g)
  have eqsum (g : ZMod p) : ∑ s ∈ fiber 0, F s = ∑ s ∈ fiber g, F s := by
    apply sum_nbij' (List.map (shift g)) (List.map (shift (-g)))
    · intro s hs
      obtain ⟨hk, he⟩ := mem_filter.mp hs
      refine mem_filter.mpr ⟨(aff s g).mpr hk, ?_⟩
      rw [phase_shift _ (mem_erase.mp hk).1, he, add_zero]
    · intro s hs
      obtain ⟨hk, he⟩ := mem_filter.mp hs
      refine mem_filter.mpr ⟨(aff s (-g)).mpr hk, ?_⟩
      rw [phase_shift _ (mem_erase.mp hk).1, he, neg_add_cancel]
    · intro s _
      simp [List.map_map, Function.comp_def, shift]
    · intro s _
      simp [List.map_map, Function.comp_def, shift]
    · intro s hs
      exact (inv s (mem_erase.mp (mem_filter.mp hs).1).2 g).symm
  have part : ∑ s ∈ K', F s = 0 := calc
    _ = ∑ g : ZMod p, ∑ s ∈ fiber g, F s := by
      simp only [fiber, sum_filter]
      rw [sum_comm]
      simp
    _ = ∑ _g : ZMod p, ∑ s ∈ fiber 0, F s := by simp_rw [← eqsum]
    _ = 0 := by simp [ZMod.card]
  have hempty : [] ∈ K := mem_faces.mpr ⟨.nil, by simp⟩
  have one := sum_erase_add K F hempty
  change (∑ s ∈ K', F s) + F [] = _ at one
  rw [part, zero] at one
  simp [F, pullback, pull, basis] at one

/-! ## Monochromatic matchings and multiplication of their sizes -/

private def bound (k r t : ℕ) := k * r + (t - 1) * (k - 1)

private def HasMatching {α : Type} (s : Finset α) (k r : ℕ) {t : ℕ}
    (c : Finset α → Fin t) (i : Fin t) :=
  ∃ f : Fin k → Finset α,
    (∀ j, f j ⊆ s ∧ (f j).card = r ∧ c (f j) = i) ∧ Pairwise (Disjoint on f)

private def AtMultiplicity (k : ℕ) :=
  ∀ {α : Type} (s : Finset α) (r t : ℕ), 0 < r → 0 < t → bound k r t ≤ s.card →
    ∀ c : Finset α → Fin t, ∃ i, HasMatching s k r c i

/-- Color each larger set by the color of a size-`b` matching inside it. A matching of `a`
larger sets in this coloring then supplies the `a * b` disjoint small sets. -/
private theorem at_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (A : AtMultiplicity a) (B : AtMultiplicity b) : AtMultiplicity (a * b) := by
  classical
  intro α s r t hr ht hn c
  let R := bound b r t
  have hR : 0 < R := Nat.add_pos_left (Nat.mul_pos hb hr) _
  have eqn : bound a R t = bound (a * b) r t := by
    obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
    obtain ⟨v, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
    simp only [bound, R, Nat.succ_sub_one]
    rw [show (u + 1) * (v + 1) - 1 = u * v + u + v by
      rw [Nat.mul_add, Nat.add_mul]; simp; omega]
    simp only [Nat.succ_eq_add_one]
    ring
  have hin (S : Finset α) (hS : S.card = R) : ∃ i, HasMatching S b r c i :=
    B S r t hr ht (by rw [hS]) c
  let C (S : Finset α) : Fin t := if h : S.card = R then (hin S h).choose else ⟨0, ht⟩
  obtain ⟨i, S, hS, hdis⟩ := A s R t hR ht (eqn ▸ hn) C
  have hinner (j : Fin a) : HasMatching (S j) b r c i := by
    rw [← (hS j).2.2]
    simpa [C, (hS j).2.1] using (hin (S j) (hS j).2.1).choose_spec
  choose f hf hd using hinner
  let F (j : Fin a × Fin b) := f j.1 j.2
  have hp : Pairwise (Disjoint on F) := by
    rintro ⟨j, u⟩ ⟨l, v⟩ huv
    by_cases hj : j = l
    · subst l
      exact hd j (fun h => huv (Prod.ext rfl h))
    · exact (hdis hj).mono (hf j u).1 (hf l v).1
  refine ⟨i, F ∘ finProdFinEquiv.symm, fun j => ?_, ?_⟩
  · exact ⟨(hf _ _).1.trans (hS _).1, (hf _ _).2⟩
  · exact fun _ _ hij => hp (finProdFinEquiv.symm.injective.ne hij)

private theorem at_zero : AtMultiplicity 0 := by
  intro α s r t hr ht hn c
  exact ⟨⟨0, ht⟩, Fin.elim0, fun j => j.elim0, fun i => Fin.elim0 i⟩

private theorem at_one : AtMultiplicity 1 := by
  intro α s r t hr ht hn c
  obtain ⟨u, hu, hcard⟩ := Finset.exists_subset_card_eq (s := s) (n := r)
    (by simpa [bound] using hn)
  exact ⟨c u, fun _ => u, fun _ => ⟨hu, hcard, rfl⟩, fun _ _ h => (h (Subsingleton.elim ..)).elim⟩


/-! ## The coloring of partial partitions for a prime matching size -/

private def block {m p : ℕ} (s : List (Vertex m p)) (g : ZMod p) : Finset (Fin (m + 1)) :=
  univ.filter (fun a => (a, g) ∈ s)

private lemma block_disjoint {m p : ℕ} {s : List (Vertex m p)} (hs : Descending level s)
    {g h : ZMod p} (hne : g ≠ h) : Disjoint (block s g) (block s h) := by
  rw [Finset.disjoint_left]
  intro x hg hh
  have xg := (mem_filter.mp hg).2
  have xh := (mem_filter.mp hh).2
  clear hg hh
  induction s with
  | nil => simp at xg
  | cons a s ih =>
    obtain ⟨ha, hs⟩ := List.pairwise_cons.mp hs
    rcases List.mem_cons.mp xg with rfl | hg <;> rcases List.mem_cons.mp xh with e | hh
    · exact hne (congrArg Prod.snd e).symm
    · exact lt_irrefl _ (ha (x, h) hh)
    · subst a
      exact lt_irrefl _ (ha (x, g) hg)
    · exact ih hs hg hh

/-- The blocks containing an `r`-set of color `i`. -/
private def rows {m p r t : ℕ} [NeZero p] (c : Finset (Fin (m + 1)) → Fin t)
    (s : List (Vertex m p)) (i : Fin t) : Finset (ZMod p) := by
  classical
  exact univ.filter (fun g => ∃ e ∈ (block s g).powersetCard r, c e = i)

private lemma mem_rows {m p r t : ℕ} [NeZero p] {c : Finset (Fin (m + 1)) → Fin t}
    {s : List (Vertex m p)} {i : Fin t} {g : ZMod p} :
    g ∈ rows (r := r) c s i ↔ ∃ e, e ⊆ block s g ∧ e.card = r ∧ c e = i := by
  simp [rows, and_assoc]

private lemma rows_mono {m p r t : ℕ} [NeZero p] (c : Finset (Fin (m + 1)) → Fin t)
    {s u : List (Vertex m p)} (hu : u.Sublist s) (i : Fin t) :
    rows (r := r) c u i ⊆ rows (r := r) c s i := by
  intro g hg
  obtain ⟨e, he, hn, hc⟩ := mem_rows.mp hg
  refine mem_rows.mpr ⟨e, ?_, hn, hc⟩
  exact fun x hx => mem_filter.mpr ⟨mem_univ _, hu.subset (mem_filter.mp (he hx)).2⟩

private lemma rows_map {m p r t : ℕ} [NeZero p] (c : Finset (Fin (m + 1)) → Fin t)
    (s : List (Vertex m p)) (i : Fin t) (g : ZMod p) :
    rows (r := r) c (s.map (shift g)) i = (rows (r := r) c s i).image (g + ·) := by
  classical
  have block_eq (h : ZMod p) : block (s.map (shift g)) (g + h) = block s h := by
    ext a
    simp only [block, mem_filter, mem_univ, true_and]
    change shift g (a, h) ∈ s.map (shift g) ↔ _
    exact List.mem_map_of_injective (shift_inj g)
  ext h
  obtain ⟨a, rfl⟩ : ∃ a, h = g + a := ⟨h - g, by abel⟩
  have h : g + a ∈ (rows (r := r) c s i).image (g + ·) ↔ a ∈ rows (r := r) c s i := by
    simp
  rw [h, mem_rows, mem_rows, block_eq]

private lemma row_lt {m p r t : ℕ} [Fact p.Prime] (c : Finset (Fin (m + 1)) → Fin t)
    (no : ¬ ∃ i, HasMatching univ p r c i) (s : List (Vertex m p)) (hs : Descending level s)
    (i : Fin t) : (rows (r := r) c s i).card < p := by
  classical
  by_contra! h
  have eq : rows (r := r) c s i = univ := eq_univ_of_card _
    (le_antisymm (card_le_univ _) (by simpa [ZMod.card] using h))
  have all (g : ZMod p) := mem_rows.mp (show g ∈ rows (r := r) c s i by rw [eq]; apply mem_univ)
  choose f hf hn hc using all
  let e := (Fintype.equivFinOfCardEq (ZMod.card p)).symm
  exact no ⟨i, f ∘ e, fun j => ⟨subset_univ _, hn _, hc _⟩,
    fun a b hab => (block_disjoint hs (e.injective.ne hab)).mono (hf _) (hf _)⟩

private lemma small_length {m p r t : ℕ} [NeZero p] (c : Finset (Fin (m + 1)) → Fin t)
    (s : List (Vertex m p)) (hs : Descending level s) (empty : ∀ i, rows (r := r) c s i = ∅) :
    s.length ≤ p * (r - 1) := by
  classical
  have hb (g : ZMod p) : (block s g).card < r := by
    by_contra! h
    obtain ⟨e, he, hn⟩ := exists_subset_card_eq h
    have hm : g ∈ rows c s (c e) := mem_rows.mpr ⟨e, he, hn, rfl⟩
    simp [empty] at hm
  have nodup : s.Nodup := hs.imp (fun h e => by subst_vars; exact lt_irrefl _ h)
  rw [← List.toFinset_card_of_nodup nodup]
  have hcard (g : ZMod p) :
      (s.toFinset.filter (fun a => a.2 = g)).card = (block s g).card := by
    apply card_nbij' Prod.fst (fun x => (x, g))
    · rintro ⟨x, h⟩ hh
      obtain ⟨hh, rfl⟩ := mem_filter.mp hh
      simpa [block] using hh
    · intro x hx
      simpa [block] using hx
    · rintro ⟨x, h⟩ hh
      exact Prod.ext rfl (mem_filter.mp hh).2.symm
    · intro x _; rfl
  have q := card_le_mul_card_image_of_maps_to (s := s.toFinset) (t := univ)
    (f := Prod.snd) (fun _ _ => mem_univ _) (r - 1) (fun g _ => by rw [hcard]; have := hb g; omega)
  simpa [ZMod.card, mul_comm] using q

private noncomputable def pickRow {I : Type} (w : I → ℕ) (i₀ : I) : I := by
  classical
  exact if h : ∃ i, 0 < w i then h.choose else i₀

private lemma pickRow_pos {I : Type} (w : I → ℕ) (i₀ : I) (h : ∃ i, 0 < w i) :
    0 < w (pickRow w i₀) := by simp [pickRow, h, h.choose_spec]

private def mean {p : ℕ} [Fact p.Prime] (S : Finset (ZMod p)) : ZMod p := (∑ x ∈ S, x) / S.card

private lemma mean_shift {p : ℕ} [Fact p.Prime] (g : ZMod p) (S : Finset (ZMod p))
    (h0 : 0 < S.card) (hp : S.card < p) : mean (S.image (g + ·)) = g + mean S := by
  have nz : (S.card : ZMod p) ≠ 0 := fun h =>
    hp.not_ge (Nat.le_of_dvd h0 ((ZMod.natCast_eq_zero_iff _ _).mp h))
  simp only [mean, card_image_of_injective _ (add_right_injective g),
    sum_image (fun _ _ _ _ h => add_left_cancel h)]
  field_simp
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_comm]


/-- In a partial partition with no colored edge, rank by the number of assigned vertices.
Once a colored edge appears, rank by the total number of color-block incidences. Equal ranks
on comparable partitions preserve all the incidences, hence also the chosen phase. -/
private theorem prime_fin {m p r t : ℕ} [Fact p.Prime] (hr : 0 < r) (ht : 0 < t)
    (hn : bound p r t ≤ m + 1) (c : Finset (Fin (m + 1)) → Fin t) :
    ∃ i, HasMatching univ p r c i := by
  classical
  by_contra no
  let size (s : List (Vertex m p)) (i : Fin t) := (rows (r := r) c s i).card
  let score (s : List (Vertex m p)) := ∑ i, size s i
  let A := p * (r - 1)
  let height (s : List (Vertex m p)) := if score s = 0 then s.length else A + score s
  let row (s : List (Vertex m p)) := pickRow (size s) ⟨0, ht⟩
  -- A nonempty proper subset of the prime field has a translation-equivariant mean.
  let phase (s : List (Vertex m p)) := if score s = 0 then (s.head?.map Prod.snd).getD 0
    else mean (rows (r := r) c s (row s))
  let L (s : List (Vertex m p)) : Vertex m p :=
    (⟨min (height s - 1) m, Nat.lt_succ_of_le (min_le_right ..)⟩, phase s)
  have capacity : A + t * (p - 1) ≤ m := by
    have hp := (Fact.out (p := p.Prime)).pos
    obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    obtain ⟨v, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
    obtain ⟨w, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
    simp only [A, bound, Nat.succ_sub_one, Nat.succ_eq_add_one] at hn ⊢
    nlinarith
  have small (s : List (Vertex m p)) (hs : Descending level s) (h : score s = 0) :
      s.length ≤ A := by
    apply small_length c s hs
    intro i
    apply card_eq_zero.mp
    have := single_le_sum (f := size s) (fun j _ => Nat.zero_le _) (mem_univ i)
    exact le_zero_iff.mp (this.trans_eq h)
  have upper (s : List (Vertex m p)) (hs : Descending level s) : height s ≤ m := by
    dsimp only [height]
    split_ifs with h
    · exact (small s hs h).trans (by omega)
    · have le : score s ≤ ∑ _i : Fin t, (p - 1) :=
        sum_le_sum (fun i _ => Nat.le_sub_one_of_lt (row_lt c no s hs i))
      simp at le
      omega
  have val (s : List (Vertex m p)) (hs : Descending level s) : level (L s) = height s - 1 :=
    min_eq_left (by have := upper s hs; omega)
  have pos (s : List (Vertex m p)) (hne : s ≠ []) : 0 < height s := by
    simp only [height]
    split_ifs with h
    · exact List.length_pos_iff.mpr hne
    · omega
  apply no_label L
  · intro s hs ne
    rw [val s hs]
    have := pos s ne
    have := upper s hs
    omega
  · intro s hs u hu ne
    have us : Descending level u := hs.sublist hu
    have le (i : Fin t) : size u i ≤ size s i := card_le_card (rows_mono c hu i)
    have total : score u ≤ score s := sum_le_sum (fun i _ => le i)
    have hlt (h : height u < height s) : RankGE level (L s) (L u) := by
      left
      rw [val s hs, val u us]
      have := pos u ne
      omega
    by_cases es : score s = 0
    · have eu : score u = 0 := by omega
      rcases lt_or_eq_of_le hu.length_le with lt | eq
      · exact hlt (by simpa only [height, eu, es, ite_true] using lt)
      · exact Or.inr (congrArg L (hu.eq_of_length eq)).symm
    by_cases eu : score u = 0
    · apply hlt
      simp only [height, eu, es, ite_true, ite_false]
      have := small u us eu
      omega
    rcases lt_or_eq_of_le total with lt | eq
    · exact hlt (by simpa [height, eu, es] using lt)
    · have eqr : rows (r := r) c u = rows (r := r) c s := by
        funext i
        apply eq_of_subset_of_card_le (rows_mono c hu i)
        change size s i ≤ size u i
        by_contra! h
        exact eq.not_lt (sum_lt_sum (fun j _ => le j) ⟨i, mem_univ _, h⟩)
      right
      simp [L, height, phase, row, size, eq, es, eqr]
  · intro s hs ne g
    have sizes : size (s.map (shift g)) = size s := by
      funext i
      exact (congrArg Finset.card (rows_map (r := r) c s i g)).trans
        (card_image_of_injective _ (add_right_injective g))
    have sc : score (s.map (shift g)) = score s := by simp [score, sizes]
    have heights : height (s.map (shift g)) = height s := by simp [height, sc]
    apply Prod.ext
    · simp [L, shift, heights]
    · change phase (s.map (shift g)) = g + phase s
      simp only [phase, sc]
      split_ifs with h
      · cases s <;> simp_all [shift]
      · have active : ∃ i, 0 < size s i := by
          by_contra! none
          exact h (by simp [score, fun i => Nat.eq_zero_of_le_zero (none i)])
        rw [show row (s.map (shift g)) = row s by simp [row, sizes], rows_map]
        exact mean_shift g _ (pickRow_pos _ _ active) (row_lt c no s hs _)

private theorem at_prime {p : ℕ} (hp : p.Prime) : AtMultiplicity p := by
  classical
  intro α s r t hr ht hn c
  have : Fact p.Prime := ⟨hp⟩
  have hs : 0 < s.card := (Nat.add_pos_left (Nat.mul_pos hp.pos hr) _).trans_le hn
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  let e : Fin (m + 1) ↪ α :=
    (Fintype.equivFinOfCardEq ((Fintype.card_coe s).trans hm)).symm.toEmbedding.trans
      (Function.Embedding.subtype _)
  obtain ⟨i, f, hf, hd⟩ := prime_fin (p := p) hr ht (hn.trans_eq hm) (fun S => c (S.map e))
  refine ⟨i, fun j => (f j).map e, fun j => ⟨?_, by simpa using (hf j).2.1, (hf j).2.2⟩, ?_⟩
  · intro x hx
    obtain ⟨a, -, rfl⟩ := mem_map.mp hx
    exact ((Fintype.equivFinOfCardEq ((Fintype.card_coe s).trans hm)).symm a).property
  · exact fun _ _ h => (disjoint_map e).mpr (hd h)

/--
**Alon–Frankl–Lovász theorem on Kneser hypergraphs.** For all natural numbers $n, k, r, t$ with
$r \ge 1$, $t \ge 1$ and $n \ge kr + (t - 1)(k - 1)$, every coloring of the $r$-element subsets
of $\{0, \dots, n - 1\}$ with $t$ colors has a color class containing $k$ pairwise disjoint
$r$-element subsets.

Alon, Frankl and Lovász proved this for all positive $n, k, r, t$ (Theorem 1.1; the case $k = 2$
is Lovász's proof of Kneser's conjecture), and the bound on $n$ is sharp; erdosproblems.com/780
lists the problem as proved.

Source: T. F. Bloom, Erdős Problems, Problem
#780, https://www.erdosproblems.com/780 (status PROVED); resolution: N. Alon, P. Frankl and L.
Lovász, The chromatic number of Kneser hypergraphs, Trans. Amer. Math. Soc. 298 (1986), 359-370,
Theorem 1.1: for positive integers n, k, r, t with n ≥ kr + (t - 1)(k - 1), if the r-subsets of an
n-element set are partitioned into t families then one family contains k pairwise disjoint r-sets
(conjectured by Erdős in 1973; k = 2 is Kneser's conjecture, proved by Lovász),
https://web.math.princeton.edu/~nalon/PDFS/Publications/The%20chromatic%20number%20of%20Kneser%20hypergraphs.pdf.
-/
public theorem kneserHypergraphColoring_holds : kneserHypergraphColoring := by
  classical
  intro n k r t hr ht hn c
  have A : AtMultiplicity k := by
    apply Nat.prime_composite_induction (motive := AtMultiplicity) @at_zero @at_one
    · exact @at_prime
    · intro a ha A b hb B
      exact at_mul (by omega) (by omega) A B
  obtain ⟨i, f, hf, hd⟩ := A (univ : Finset (Fin n)) r t hr ht (by simpa [bound] using hn) c
  have inj : Function.Injective f := by
    intro a b he
    by_contra h
    have hdis := hd h
    change Disjoint (f a) (f b) at hdis
    rw [he, disjoint_self] at hdis
    have hzero := Finset.card_eq_zero.mpr hdis
    have := (hf b).2.1
    omega
  refine ⟨i, univ.image f, ?_, by simp [card_image_of_injective _ inj], ?_, ?_⟩
  · intro e he
    obtain ⟨j, -, rfl⟩ := mem_image.mp he
    exact mem_powersetCard.mpr ⟨(hf j).1, (hf j).2.1⟩
  · intro e he
    obtain ⟨j, -, rfl⟩ := mem_image.mp he
    exact (hf j).2.2
  · intro e he g hg heg
    obtain ⟨j, -, rfl⟩ := mem_image.mp he
    obtain ⟨l, -, rfl⟩ := mem_image.mp hg
    exact hd (fun h => heg (congrArg f h))

end MathlibExt.Combinatorics.KneserHypergraphColoringErdosProblem780Wanted
