/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group

/-!
# Finitely presented elementary amenable groups (Kourovka Notebook Problem 16.52)

Kourovka Notebook, Archive of Solved Problems, Problem 16.52 (P. Linnell, T. Schick): is every
finitely presented elementary amenable group solvable-by-finite?

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.52 (P.
Linnell, T. Schick). UnsolvedMath record UM-00701244 (`KOU-16.52`), dataset ulamai/UnsolvedMath
v1.8.0.

Elementary amenable groups are the smallest class containing finite and abelian groups and closed
under isomorphisms, subgroups, quotients, extensions and directed unions (Chou), an inductive
predicate on groups in `Type`. Solvable-by-finite means having a solvable subgroup of finite index
(its normal core is a solvable normal subgroup of finite index).

The theorem `finitelyPresentedElementaryAmenableVirtuallySolvable_refuted` uses a group on three
generators with six relators. Its adjacent swaps generate a locally finite subgroup. Adjoining a
translation and then an insertion gives two ascending extensions, so the group is elementary
amenable. Its action on a line and a spare ray contains alternating groups of unbounded order,
which rules out solvability of any finite-index subgroup.

The permutation action is modeled on Houghton's eventual translations, as described in
S. R. Lee, *Geometry of Houghton's Groups*, https://arxiv.org/abs/1212.0257.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.ElementaryAmenableVirtuallySolvableKourovka16Problem52Wanted

/-- **Elementary amenable groups.** The class of elementary amenable groups is the smallest class
of groups that contains every finite group and every abelian group and is closed under
isomorphisms, subgroups, quotients, extensions and directed unions. Closure under extensions means
that a group $G$ with a normal subgroup $N$ is elementary amenable whenever $N$ and $G/N$ are;
closure under directed unions means that $G$ is elementary amenable whenever it is the union of a
family of elementary amenable subgroups that is directed under inclusion. -/
inductive IsElementaryAmenable : (G : Type) → [Group G] → Prop
  | of_finite (G : Type) [Group G] [Finite G] : IsElementaryAmenable G
  | of_comm (G : Type) [Group G] (h : ∀ a b : G, a * b = b * a) : IsElementaryAmenable G
  | of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) :
      IsElementaryAmenable G → IsElementaryAmenable H
  | subgroup {G : Type} [Group G] (K : Subgroup G) : IsElementaryAmenable G → IsElementaryAmenable K
  | quotient {G : Type} [Group G] (N : Subgroup G) [N.Normal] :
      IsElementaryAmenable G → IsElementaryAmenable (G ⧸ N)
  | extension {G : Type} [Group G] (N : Subgroup G) [N.Normal] :
      IsElementaryAmenable N → IsElementaryAmenable (G ⧸ N) → IsElementaryAmenable G
  | directedUnion {G : Type} [Group G] (S : Set (Subgroup G)) :
      DirectedOn (· ≤ ·) S → (∀ K ∈ S, IsElementaryAmenable K) → (∀ g : G, ∃ K ∈ S, g ∈ K) →
      IsElementaryAmenable G

/-- **Kourovka Problem 16.52 (Linnell–Schick).** The statement that every finitely presented
elementary amenable group $G$ is solvable-by-finite, that is, $G$ has a solvable subgroup of finite
index. -/
def finitelyPresentedElementaryAmenableVirtuallySolvable : Prop :=
  ∀ (G : Type) [Group G], Group.IsFinitelyPresented G → IsElementaryAmenable G →
    ∃ N : Subgroup G, N.FiniteIndex ∧ Group.IsSolvable N

open Subgroup

variable {G : Type} [Group G]

/-- An increasing union inherits elementary amenability from its stages. -/
private theorem elementaryAmenable_iSup (B : ℕ → Subgroup G) (hm : Monotone B)
    (he : ∀ n, IsElementaryAmenable (B n)) : IsElementaryAmenable (⨆ n, B n : Subgroup G) := by
  let U := ⨆ n, B n
  let S (n : ℕ) := (B n).subgroupOf U
  apply IsElementaryAmenable.directedUnion (Set.range S)
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact ⟨_, ⟨max i j, rfl⟩, fun _ hx ↦ hm (le_max_left ..) hx,
      fun _ hx ↦ hm (le_max_right ..) hx⟩
  · rintro _ ⟨n, rfl⟩
    exact .of_mulEquiv (subgroupOfEquivOfLe (le_iSup B n)).symm (he n)
  · intro g
    obtain ⟨n, hn⟩ := (mem_iSup_of_directed hm.directed_le).mp g.property
    exact ⟨_, ⟨n, rfl⟩, hn⟩

/-- If conjugation by the extra generator sends the base into itself, its inverse conjugates
form an increasing union. This union is normal, and the quotient is cyclic. -/
private theorem elementaryAmenable_of_ascending (B : Subgroup G) (t : G)
    (hb : IsElementaryAmenable B)
    (hc : B.map (MulAut.conj t) ≤ B) (ht : B ⊔ zpowers t = ⊤) : IsElementaryAmenable G := by
  let u := MulAut.conj t
  let S (n : ℕ) := B.map (u.symm ^ n : MulAut G).toMonoidHom
  have h0 : S 0 = B := by
    dsimp only [S, pow_zero]
    exact B.map_id
  have hnext (n : ℕ) : S (n + 1) = (S n).map u.symm.toMonoidHom := by
    dsimp only [S]
    rw [map_map]
    congr 1
    change (u.symm ^ (n + 1) : MulAut G).toMonoidHom = (u.symm * u.symm ^ n).toMonoidHom
    rw [pow_succ']
  have hbase : S 0 ≤ S 1 := by
    rw [hnext, h0]
    intro g hg
    exact ⟨u g, hc ⟨g, hg, rfl⟩, u.symm_apply_apply g⟩
  have hm : Monotone S := by
    apply monotone_nat_of_le_succ
    intro n
    induction n with
    | zero => exact hbase
    | succ n ih => simpa only [hnext] using map_mono (f := u.symm.toMonoidHom) ih
  let K := ⨆ n, S n
  have hbK : B ≤ K := h0 ▸ le_iSup S 0
  have htN : t ∈ normalizer (K : Set G) := by
    rw [mem_normalizer_iff'']
    intro g
    change g ∈ K ↔ u.symm g ∈ K
    constructor
    · intro hg
      obtain ⟨n, hn⟩ := (mem_iSup_of_directed hm.directed_le).mp hg
      apply le_iSup S (n + 1)
      rw [hnext]
      exact ⟨g, hn, rfl⟩
    · intro hg
      obtain ⟨n, hn⟩ := (mem_iSup_of_directed hm.directed_le).mp hg
      have hh := hm (Nat.le_succ n) hn
      rw [hnext, mem_map_equiv] at hh
      exact le_iSup S n (by simpa using hh)
  have : K.Normal := normalizer_eq_top_iff.mp (top_unique (ht ▸ sup_le
    (hbK.trans K.le_normalizer) (zpowers_le.mpr htN)))
  apply IsElementaryAmenable.extension K (elementaryAmenable_iSup S hm fun n ↦
    .of_mulEquiv ((u.symm ^ n : MulAut G).subgroupMap B) hb)
  let q := QuotientGroup.mk' K
  have : IsCyclic (G ⧸ K) := by
    apply isCyclic_iff_exists_zpowers_eq_top.mpr
    refine ⟨q t, top_unique ?_⟩
    rintro x -
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K x
    have hle : ⊤ ≤ (zpowers (q t)).comap q := by
      rw [← ht, sup_le_iff, zpowers_le]
      exact ⟨fun x hx ↦ by
        change q x ∈ zpowers (q t)
        rw [show q x = 1 from (QuotientGroup.eq_one_iff x).mpr (hbK hx)]
        exact one_mem _, mem_zpowers _⟩
    exact hle (mem_top g)
  exact .of_comm _ fun _ _ ↦ mul_comm' ..

/-- The product of adjacent swaps in descending order, ending with the zeroth swap. -/
private def prefixWord (x : ℕ → G) : ℕ → G
  | 0 => 1
  | n + 1 => x n * prefixWord x n

private theorem commute_prefixWord (x : ℕ → G)
    (far : ∀ i j, i + 1 < j → Commute (x i) (x j))
    {k i : ℕ} (hi : k < i) : Commute (x i) (prefixWord x k) := by
  induction k with
  | zero => exact Commute.one_right _
  | succ k ih => exact ((far k i hi).symm).mul_right (ih (by omega))

private theorem mul_prefixWord_of_lt (x : ℕ → G) (far : ∀ i j, i + 1 < j → Commute (x i) (x j))
    (braid : ∀ i, x i * x (i + 1) * x i = x (i + 1) * x i * x (i + 1))
    {i k : ℕ} (hi : i + 1 < k) : x i * prefixWord x k = prefixWord x k * x (i + 1) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases (show i + 1 ≤ k by omega).eq_or_lt with rfl | h
    · simp only [prefixWord]
      rw [← mul_assoc, ← mul_assoc, ← mul_assoc, braid i]
      simp only [mul_assoc, (commute_prefixWord x far (Nat.lt_succ_self i)).eq]
    · rw [prefixWord, ← mul_assoc, (far i k h).eq, mul_assoc, ih h, mul_assoc]

private def firstSwaps (x : ℕ → G) (n : ℕ) : Subgroup G :=
  closure (x '' Set.Iio n)

/-- In a group satisfying the type A Coxeter relations, each finite initial segment of the
generators generates a finite subgroup. The prefix words represent the cosets of the subgroup
generated by all but the first swap. -/
private theorem finite_firstSwaps (x : ℕ → G) (sq : ∀ i, x i * x i = 1)
    (braid : ∀ i, x i * x (i + 1) * x i = x (i + 1) * x i * x (i + 1))
    (far : ∀ i j, i + 1 < j → Commute (x i) (x j)) (n : ℕ) : Finite (firstSwaps x n) := by
  induction n generalizing x with
  | zero =>
    rw [show firstSwaps x 0 = ⊥ by simp [firstSwaps]]
    infer_instance
  | succ n ih =>
    let H := firstSwaps (fun j ↦ x (j + 1)) n
    have : Finite H := ih _ (fun i ↦ sq (i + 1)) (fun i ↦ braid (i + 1))
      (fun i j h ↦ far (i + 1) (j + 1) (by omega))
    let Z (g : G) := ∃ k ≤ n + 1, ∃ h ∈ H, g = prefixWord x k * h
    -- Left multiplication by a swap preserves the union of the indicated cosets.
    have step (i : ℕ) (hi : i < n + 1) (g : G) (hg : Z g) : Z (x i * g) := by
      obtain ⟨k, hk, h, hh, rfl⟩ := hg
      rcases lt_trichotomy k i with hk' | rfl | hk'
      · refine ⟨k, hk, x i * h, H.mul_mem ?_ hh, ?_⟩
        · apply Subgroup.subset_closure
          exact ⟨i - 1, by change i - 1 < n; omega, congrArg x (by omega)⟩
        · rw [← mul_assoc, (commute_prefixWord x far hk').eq, mul_assoc]
      · exact ⟨k + 1, by omega, h, hh, (mul_assoc ..).symm⟩
      · rcases (show i + 1 ≤ k by omega).eq_or_lt with rfl | hlt
        · refine ⟨i, by omega, h, hh, ?_⟩
          simp [prefixWord, ← mul_assoc, sq]
        · refine ⟨k, hk, x (i + 1) * h, H.mul_mem (Subgroup.subset_closure ⟨i, ?_, rfl⟩) hh, ?_⟩
          · change i < n
            omega
          · rw [← mul_assoc, mul_prefixWord_of_lt x far braid hlt, mul_assoc]
    have covers (g : firstSwaps x (n + 1)) : Z g.val := by
      refine closure_induction_left (p := fun g _ ↦ Z g) ?_ ?_ ?_ g.property
      · exact ⟨0, by omega, 1, one_mem _, by simp [prefixWord]⟩
      · rintro _ ⟨i, hi, rfl⟩ g _ hg
        exact step i hi g hg
      · rintro _ ⟨i, hi, rfl⟩ g _ hg
        rw [inv_eq_of_mul_eq_one_right (sq i)]
        exact step i hi g hg
    classical
    choose k hk h hh eqn using covers
    let coordinates (g : firstSwaps x (n + 1)) : Fin (n + 2) × H :=
      (⟨k g, Nat.lt_succ_of_le (hk g)⟩, ⟨h g, hh g⟩)
    apply Finite.of_injective coordinates
    intro g f he
    apply Subtype.ext
    rw [eqn g, eqn f]
    have he₁ := congrArg (fun z : Fin (n + 2) × H ↦ z.1.val) he
    have he₂ := congrArg (fun z : Fin (n + 2) × H ↦ z.2.val) he
    exact congrArg₂ (fun i v ↦ prefixWord x i * v) he₁ he₂

private def adj (a t : G) : ℕ → G
  | 0 => a
  | n + 1 => MulAut.conj t (adj a t n)

/-- The first three relations are local Coxeter relations. The insertion fixes the first swap,
sends the third to the fourth, and conjugates the translation to a swap times the translation. -/
private def relations (a t s : G) : Fin 6 → G × G :=
  let x := adj a t
  ![(a * a, 1), (a * x 1 * a, x 1 * a * x 1), (a * x 2, x 2 * a),
    (MulAut.conj s a, a), (MulAut.conj s (x 2), x 3), (MulAut.conj s t, x 2 * t)]

private def word (v : Fin 3 → G) (i : Fin 6) : G :=
  let r := relations (v 0) (v 1) (v 2) i
  r.1 * r.2⁻¹

private theorem word_map {H : Type} [Group H] (f : G →* H) (v : Fin 3 → G) (i : Fin 6) :
    f (word v i) = word (f ∘ v) i := by
  fin_cases i <;> simp [word, relations, adj, MulAut.conj_apply]

private abbrev relators := Set.range (word (FreeGroup.of : Fin 3 → _))

/-- Our abstract finitely presented group acts on a line and a spare ray. -/
private abbrev P := PresentedGroup relators

private abbrev a : P := PresentedGroup.of 0
private abbrev t : P := PresentedGroup.of 1
private abbrev s : P := PresentedGroup.of 2
private abbrev x := adj a t

private theorem rel (i : Fin 6) : (relations a t s i).1 = (relations a t s i).2 := by
  have h := PresentedGroup.one_of_mem (rels := relators) (Set.mem_range_self i)
  rw [word_map] at h
  exact mul_inv_eq_one.mp h

/-- Conjugating by the insertion increases the separation of disjoint swaps by one. -/
private theorem commute_and_conj_shift (k : ℕ) :
    Commute a (x (k + 2)) ∧ MulAut.conj s (x (k + 2)) = x (k + 3) := by
  induction k with
  | zero => exact ⟨rel 2, rel 4⟩
  | succ k ih =>
    have hc : Commute (x 2) (x (k + 4)) :=
      (ih.1.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom
    constructor
    · have h := ih.1.map (MulAut.conj s).toMonoidHom
      change Commute (MulAut.conj s a) (MulAut.conj s (x (k + 2))) at h
      rwa [show MulAut.conj s a = a from rel 3, ih.2] at h
    · change MulAut.conj s (t * x (k + 2) * t⁻¹) = x (k + 4)
      rw [map_mul, map_mul, map_inv, show MulAut.conj s t = x 2 * t from rel 5, ih.2]
      calc
        _ = x 2 * (t * x (k + 3) * t⁻¹) * (x 2)⁻¹ := by group
        _ = x (k + 4) := by
          change x 2 * x (k + 4) * (x 2)⁻¹ = _
          rw [hc.eq, mul_inv_cancel_right]

private theorem coxeter_relations :
    (∀ i, x i * x i = 1) ∧
    (∀ i, x i * x (i + 1) * x i = x (i + 1) * x i * x (i + 1)) ∧
    (∀ i j, i + 1 < j → Commute (x i) (x j)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    induction i with
    | zero => exact rel 0
    | succ i ih =>
      change MulAut.conj t (x i) * MulAut.conj t (x i) = 1
      rw [← map_mul, ih, map_one]
  · intro i
    induction i with
    | zero => exact rel 1
    | succ i ih =>
      have h := congrArg (MulAut.conj t) ih
      simp only [map_mul] at h
      exact h
  · intro i
    induction i with
    | zero =>
      intro j hj
      change Commute a (x j)
      simpa only [show j - 2 + 2 = j by omega] using (commute_and_conj_shift (j - 2)).1
    | succ i ih =>
      rintro (_ | j) hj
      · omega
      exact (ih j (by omega)).map (MulAut.conj t).toMonoidHom

private theorem elementaryAmenable_of_swaps (y : ℕ → G) (v : G)
    (shift : ∀ i, MulAut.conj v (y i) = y (i + 1))
    (sq : ∀ i, y i * y i = 1)
    (braid : ∀ i, y i * y (i + 1) * y i = y (i + 1) * y i * y (i + 1))
    (far : ∀ i j, i + 1 < j → Commute (y i) (y j))
    (gen : ∀ H : Subgroup G, y 0 ∈ H → v ∈ H → H = ⊤) : IsElementaryAmenable G := by
  let U := ⨆ n, firstSwaps y n
  have hm : Monotone (firstSwaps y) := fun _ _ h ↦
    closure_mono (Set.image_mono (Set.Iio_subset_Iio h))
  have allmem (i : ℕ) : y i ∈ U := le_iSup (firstSwaps y) (i + 1)
    (Subgroup.subset_closure ⟨i, Nat.lt_succ_self _, rfl⟩)
  apply elementaryAmenable_of_ascending U v
  · exact elementaryAmenable_iSup _ hm fun n ↦ by
      have := finite_firstSwaps y sq braid far n
      exact .of_finite _
  · rw [map_le_iff_le_comap]
    apply iSup_le
    intro n
    apply (Subgroup.closure_le _).2
    rintro _ ⟨i, _, rfl⟩
    change MulAut.conj v (y i) ∈ U
    rw [shift]
    exact allmem _
  · exact gen _ (mem_sup_left (allmem 0)) (mem_sup_right (mem_zpowers v))

/-- First adjoin the translation to the increasing union of the finite swap groups,
then adjoin the insertion to the subgroup generated by the translation and the first swap. -/
private theorem elementaryAmenable_presented : IsElementaryAmenable P := by
  let B : Subgroup P := closure {a, t}
  have ha : a ∈ B := Subgroup.subset_closure (by simp)
  have ht : t ∈ B := Subgroup.subset_closure (by simp)
  have hx (i : ℕ) : x i ∈ B := by
    induction i with
    | zero => exact ha
    | succ i ih => exact B.mul_mem (B.mul_mem ht ih) (B.inv_mem ht)
  apply elementaryAmenable_of_ascending B s
  · apply elementaryAmenable_of_swaps (fun i ↦ (⟨x i, hx i⟩ : B)) ⟨t, ht⟩ (fun _ ↦ rfl)
      (fun i ↦ Subtype.ext (coxeter_relations.1 i)) (fun i ↦ Subtype.ext (coxeter_relations.2.1 i))
      (fun i j h ↦ Subtype.ext (coxeter_relations.2.2 i j h).eq)
    intro H ha' ht'
    have hle : B ≤ H.map B.subtype := by
      apply (Subgroup.closure_le _).2
      rintro g (rfl | rfl)
      · exact ⟨_, ha', rfl⟩
      · exact ⟨_, ht', rfl⟩
    apply top_unique
    rintro g -
    obtain ⟨y, hy, eqn⟩ := hle g.property
    exact (Subtype.ext eqn : y = g) ▸ hy
  · rw [map_le_iff_le_comap]
    apply (Subgroup.closure_le _).2
    rintro g (rfl | rfl)
    · change MulAut.conj s a ∈ B
      rwa [show MulAut.conj s a = a from rel 3]
    · change MulAut.conj s t ∈ B
      rw [show MulAut.conj s t = x 2 * t from rel 5]
      exact B.mul_mem (hx 2) ht
  · apply top_unique
    intro g _
    apply PresentedGroup.generated_by
    intro i
    fin_cases i
    · exact mem_sup_left ha
    · exact mem_sup_left ht
    · exact mem_sup_right (mem_zpowers s)

private abbrev Y := ℤ ⊕ ℕ

private def trans : Equiv.Perm Y := (Equiv.addRight (1 : ℤ)).sumCongr (Equiv.refl ℕ)

/-- Insert a point at 2 on the integer line, taking the point from the spare ray. -/
private def ins : Equiv.Perm Y where
  toFun
    | .inl i => if i < 2 then .inl i else .inl (i + 1)
    | .inr 0 => .inl 2
    | .inr (i + 1) => .inr i
  invFun
    | .inl i => if i < 2 then .inl i else if i = 2 then .inr 0 else .inl (i - 1)
    | .inr i => .inr (i + 1)
  left_inv
    | .inl i => by dsimp; split_ifs <;> grind
    | .inr 0 => by decide
    | .inr (i + 1) => rfl
  right_inv
    | .inl i => by dsimp; split_ifs <;> grind
    | .inr i => rfl

private def swapAt (i : ℤ) : Equiv.Perm Y := Equiv.swap (.inl i) (.inl (i + 1))

private theorem trans_swap (i : ℕ) : adj (swapAt 0) trans i = swapAt i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change trans * adj (swapAt 0) trans i * trans⁻¹ = _
    rw [ih, swapAt, ← Equiv.swap_apply_apply]
    rfl

private def generators : Fin 3 → Equiv.Perm Y := ![swapAt 0, trans, ins]

private theorem satisfies (i : Fin 6) : word generators i = 1 := by
  apply mul_inv_eq_one.mpr
  change (relations (swapAt 0) trans ins i).1 = (relations (swapAt 0) trans ins i).2
  fin_cases i
  · exact Equiv.swap_mul_self _ _
  · change swapAt 0 * adj (swapAt 0) trans 1 * swapAt 0 =
      adj (swapAt 0) trans 1 * swapAt 0 * adj (swapAt 0) trans 1
    rw [trans_swap]
    ext z
    rcases eq_or_ne z (.inl 0) with rfl | h0
    · decide
    rcases eq_or_ne z (.inl 1) with rfl | h1
    · decide
    rcases eq_or_ne z (.inl 2) with rfl | h2
    · decide
    simp [swapAt, Equiv.Perm.mul_apply, Equiv.swap_apply_def, h0, h1, h2]
  · change swapAt 0 * adj (swapAt 0) trans 2 = adj (swapAt 0) trans 2 * swapAt 0
    rw [trans_swap]
    exact Equiv.mul_swap_eq_swap_mul (swapAt 0) (.inl 2) (.inl 3)
  · change ins * swapAt 0 * ins⁻¹ = swapAt 0
    rw [swapAt, ← Equiv.swap_apply_apply]
    rfl
  · change ins * adj (swapAt 0) trans 2 * ins⁻¹ = adj (swapAt 0) trans 3
    rw [trans_swap, trans_swap, swapAt, ← Equiv.swap_apply_apply]
    rfl
  · change ins * trans * ins⁻¹ = adj (swapAt 0) trans 2 * trans
    rw [trans_swap, mul_inv_eq_iff_eq_mul]
    ext z
    rcases z with i | (_ | i) <;>
      simp [Equiv.Perm.mul_apply, swapAt, Equiv.swap_apply_def, trans, ins, Equiv.addRight]
    split_ifs <;> grind

private def action : P →* Equiv.Perm Y := PresentedGroup.toGroup (f := generators) (by
  rintro _ ⟨i, rfl⟩
  rw [word_map]
  exact satisfies i)

private theorem swap_mem_range (i : ℕ) : swapAt i ∈ action.range := by
  refine ⟨x i, ?_⟩
  induction i with
  | zero => exact PresentedGroup.toGroup.of _
  | succ i ih =>
    change action (t * x i * t⁻¹) = swapAt (i + 1)
    rw [map_mul, map_mul, map_inv, ih,
      show action t = trans from PresentedGroup.toGroup.of _, swapAt, ← Equiv.swap_apply_apply]
    rfl

private def lineEmb (n : ℕ) : Fin n ↪ Y :=
  ⟨fun i ↦ .inl i.val, fun _ _ h ↦ Fin.ext (Int.ofNat_inj.mp (Sum.inl.inj h))⟩

private theorem extend_swap {n : ℕ} (i : Fin n) :
    Equiv.Perm.viaEmbeddingHom (lineEmb (n + 1)) (Equiv.swap i.castSucc i.succ) = swapAt i := by
  let e := lineEmb (n + 1)
  change (Equiv.swap i.castSucc i.succ).viaEmbedding e = Equiv.swap (e i.castSucc) (e i.succ)
  ext z
  by_cases hz : z ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hz
    rw [Equiv.Perm.viaEmbedding_apply]
    exact (e.injective.swap_apply _ _ _).symm
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hz, Equiv.swap_apply_of_ne_of_ne]
    · rintro rfl
      exact hz ⟨_, rfl⟩
    · rintro rfl
      exact hz ⟨_, rfl⟩

/-- The action contains all permutations of every finite initial interval of the line. -/
private theorem perm_embedding (n : ℕ) :
    ∃ f : Equiv.Perm (Fin (n + 1)) →* action.range, Function.Injective f := by
  let e := Equiv.Perm.viaEmbeddingHom (lineEmb (n + 1))
  have h : ⊤ ≤ action.range.toSubmonoid.comap e := by
    rw [← Equiv.Perm.mclosure_swap_castSucc_succ n, Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩
    change Equiv.Perm.viaEmbeddingHom _ _ ∈ action.range
    rw [extend_swap]
    exact swap_mem_range i
  exact ⟨e.codRestrict _ (fun g ↦ h (Submonoid.mem_top g)), fun _ _ he ↦
    Equiv.Perm.viaEmbeddingHom_injective _ (congrArg Subtype.val he)⟩

/-- A finite quotient kills each simple alternating group larger than the quotient. Thus every
finite-index subgroup contains a nonabelian simple group in its normal core. -/
private theorem not_isSolvable_of_finiteIndex (N : Subgroup action.range) [N.FiniteIndex] :
    ¬ Group.IsSolvable N := by
  classical
  intro hs
  let Q := action.range ⧸ N.normalCore
  let m := Nat.card Q
  let n := 2 * m + 5
  have hn : 5 ≤ n := by dsimp [n]; omega
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let A := alternatingGroup (Fin n)
  obtain ⟨incl, hincl⟩ := perm_embedding (2 * m + 4)
  let a : A →* action.range := incl.comp (alternatingGroup (Fin n)).subtype
  let f : A →* Q := (QuotientGroup.mk' N.normalCore).comp a
  have hc : Nat.card Q < Nat.card A := by
    rw [show Nat.card A = n.factorial / 2 by
      dsimp only [A]
      rw [nat_card_alternatingGroup, Nat.card_fin]]
    have h := Nat.lt_factorial_self (n := n) (by omega)
    change m < n.factorial / 2
    dsimp [n] at h ⊢
    omega
  have hker := alternatingGroup.normal_subgroup_eq_bot_or_eq_top (N := f.ker)
    (by simpa using hn)
  rcases hker with hbot | htop
  · exact hc.not_ge (Nat.card_le_card_of_injective f (f.ker_eq_bot_iff.mp hbot))
  · have hmem (x : A) : a x ∈ N.normalCore := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact (show x ∈ f.ker from htop ▸ Subgroup.mem_top x)
    let b := a.codRestrict N fun x ↦ N.normalCore_le (hmem x)
    have hinj : Function.Injective b := fun x y h ↦
      hincl.comp Subtype.val_injective (congrArg Subtype.val h)
    have : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective hinj
    have : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by simpa using hn)
    have : IsMulCommutative A :=
      ⟨⟨IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance⟩⟩
    have := (alternatingGroup.isMulCommutative_iff_card_le_three (α := Fin n)).mp ‹_›
    simp at this
    omega

/--
**Finitely presented elementary amenable groups need not be virtually solvable.** There is a
finitely presented elementary amenable group $G$ that is not solvable-by-finite: no subgroup of
finite index in $G$ is solvable. This answers Kourovka Problem 16.52 (P. Linnell, T. Schick) in
the negative.

As Belegradek and Cornulier observed, Houghton's groups $H_n$, finitely presented for $n \ge 3$
by Brown, are elementary amenable (the locally finite group of finitary permutations extended by
$\mathbb{Z}^{n-1}$) but not virtually solvable.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.52
(P. Linnell, T. Schick); resolution: C. H. Houghton, Arch. Math. (Basel) 31 (1978/79), 254-258; K.
S. Brown, J. Pure Appl. Algebra 44 (1987), 45-75; observation of I. Belegradek and Y. Cornulier,
MathOverflow question 107996, Kourovka Archive, Problem 16.52 (No, not every: Houghton's groups are
finitely presented (Brown) and elementary amenable, but not virtually solvable),
https://mathoverflow.net/questions/107996.
-/
public theorem finitelyPresentedElementaryAmenableVirtuallySolvable_refuted :
    ¬ finitelyPresentedElementaryAmenableVirtuallySolvable := by
  intro h
  have : Finite relators := Set.finite_range _
  obtain ⟨N, _, hs⟩ := h P inferInstance elementaryAmenable_presented
  let f := action.rangeRestrict
  have : (N.map f).FiniteIndex :=
    Subgroup.FiniteIndex.map_of_surjective N action.rangeRestrict_surjective
  exact not_isSolvable_of_finiteIndex (N.map f)
    (Group.isSolvable_of_surjective (f.subgroupMap_surjective N))

end MathlibExt.GroupTheory.ElementaryAmenableVirtuallySolvableKourovka16Problem52Wanted
