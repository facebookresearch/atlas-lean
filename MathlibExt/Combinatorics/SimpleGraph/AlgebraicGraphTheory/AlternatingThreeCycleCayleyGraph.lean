/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import MathlibExt.Combinatorics.SimpleGraph.AlgebraicGraphTheory.IntegralCayleyGraphs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.RepresentationTheory.Tannaka

/-!
# The alternating group's Cayley graph on the 3-cycles (1 2 k)

We prove integrality of the graph in Kourovka Notebook Problem 19.50(b). Write `t = (1 2)`.
The symmetric set of generators consists of `t * s` for the transpositions `s` that do not
commute with `t`. On the symmetric group the adjacency operator is thus translation by `t`
times the difference of two commuting transposition sums, one over the whole group and one
over the centralizer of `t`. Both sums have integral spectrum by the normal involution theorem.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.IntegralCayleyGraphsKourovka19Problem50Wanted

/-- **The 3-cycles (1 2 k).** For a natural number $n$, this is the set of $3$-cycles $(1\,2\,k)$
with $3 \le k \le n$ in the symmetric group $S_n$. With the points numbered $0, 1, \dots, n - 1$,
these are the permutations $(0\,1\,k) = (0\,1)(1\,k)$ with $2 \le k < n$, products composed right
to left; the set is empty when $n < 3$. -/
def threeCyclesOneTwo (n : ℕ) : Set (Equiv.Perm (Fin n)) :=
  {σ | ∃ a b k : Fin n, a.val = 0 ∧ b.val = 1 ∧ 2 ≤ k.val ∧ σ = Equiv.swap a b * Equiv.swap b k}

open Classical in
/-- **The Kourovka 19.50(b) integrality claim.** For $n \ge 3$ let $S$ be the set of $3$-cycles
$(1\,2\,k)$ with $3 \le k \le n$ on the points $1, \dots, n$, and let $R = S \cup S^{-1}$, a subset
of the alternating group $A_n$. This is the proposition that for every $n \ge 3$ the Cayley graph
$\mathrm{Cay}(A_n, R)$ is integral. Here $\mathrm{Cay}(A_n, R)$ has vertex set $A_n$, distinct $x$
and $y$ being adjacent when $x^{-1} y \in R$ or $y^{-1} x \in R$, and a graph is integral when
every eigenvalue of its integer adjacency matrix (every complex root of the characteristic
polynomial of that matrix) is an integer. -/
def alternatingThreeCycleCayleyGraphIntegral : Prop :=
  ∀ n : ℕ, 3 ≤ n → HasIntegralSpectrum ((SimpleGraph.mulCayley
    {g : alternatingGroup (Fin n) | (g : Equiv.Perm (Fin n)) ∈ threeCyclesOneTwo n ∨
      (g : Equiv.Perm (Fin n))⁻¹ ∈ threeCyclesOneTwo n}).adjMatrix ℤ)

open Module.End TannakaDuality.FiniteGroup

-- A sum of right translations, with the generators indexed in a possibly smaller group.
private noncomputable def walk {K G : Type} [Group K] [Group G] (φ : K →* G)
    (S : Set K) [Fintype S] : Module.End ℂ (G → ℂ) :=
  ∑ s : S, rightRegular (φ s)

private theorem walk_apply {K G : Type} [Group K] [Group G] (φ : K →* G)
    (S : Set K) [Fintype S] (v : G → ℂ) (x : G) :
    walk φ S v x = ∑ s : S, v (x * φ s) := by
  simp [walk, LinearMap.sum_apply, Finset.sum_apply]

private theorem cayley_walk {G : Type} [Group G] [Fintype G] [DecidableEq G]
    (S : Set G) [Fintype S] [DecidableRel (SimpleGraph.mulCayley S).Adj]
    (h1 : 1 ∉ S) (hi : ∀ g : G, g⁻¹ ∈ S ↔ g ∈ S) :
    Matrix.toLin' (((SimpleGraph.mulCayley S).adjMatrix ℤ).map (Int.castRingHom ℂ)) =
      walk (MonoidHom.id G) S := by
  classical
  refine LinearMap.ext fun v => funext fun x => ?_
  rw [walk_apply, Matrix.toLin'_apply]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, SimpleGraph.adjMatrix_apply]
  rw [← Equiv.sum_comp (Equiv.mulLeft x)]
  trans ∑ g ∈ Finset.univ.filter (· ∈ S), v (x * g)
  swap
  · exact Finset.sum_subtype _ (by simp) _
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hadj : (SimpleGraph.mulCayley S).Adj x (x * g) ↔ g ∈ S := by
    rw [SimpleGraph.mulCayley_adj, inv_mul_cancel_left, mul_inv_rev, inv_mul_cancel_right,
      hi, or_self, ne_eq, left_eq_mul]
    exact and_iff_right_of_imp fun hg he => h1 (he ▸ hg)
  simp only [Equiv.coe_mulLeft, hadj]
  split_ifs <;> simp

-- Restrict to a left coset on which the eigenvector does not vanish.
private theorem eigenvalue_walk_pullback {K G : Type} [Group K] [Group G] (φ : K →* G)
    (S : Set K) [Fintype S] {μ : ℂ} (hμ : (walk φ S).HasEigenvalue μ) :
    (walk (MonoidHom.id K) S).HasEigenvalue μ := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  obtain ⟨x, hx⟩ : ∃ x, v x ≠ 0 := Function.ne_iff.mp hv.2
  let w (g : K) := v (x * φ g)
  apply hasEigenvalue_of_hasEigenvector (x := w)
  refine ⟨mem_eigenspace_iff.mpr (funext fun g => ?_), fun h => hx ?_⟩
  · simpa [walk_apply, w, mul_assoc] using congrFun hv.apply_eq_smul (x * φ g)
  · simpa [w] using congrFun h 1

-- Conversely an eigenvector on a subgroup extends by zero to the ambient group.
private theorem eigenvalue_walk_extend {G : Type} [Group G] (H : Subgroup G)
    (S : Set H) [Fintype S] {μ : ℂ} (hμ : (walk (MonoidHom.id H) S).HasEigenvalue μ) :
    (walk H.subtype S).HasEigenvalue μ := by
  classical
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  let w (x : G) := if hx : x ∈ H then v ⟨x, hx⟩ else 0
  apply hasEigenvalue_of_hasEigenvector (x := w)
  refine ⟨mem_eigenspace_iff.mpr (funext fun x => ?_), fun h => hv.2 ?_⟩
  · by_cases hx : x ∈ H
    · have hin (s : S) : x * (s.val : G) ∈ H := H.mul_mem hx s.val.2
      calc
        _ = ∑ s : S, v ((⟨x, hx⟩ : H) * s.val) := by
          rw [walk_apply]
          exact Finset.sum_congr rfl fun s _ => dite_eq_left (hin s)
        _ = _ := by simpa [walk_apply, w, hx] using congrFun hv.apply_eq_smul (⟨x, hx⟩ : H)
    · have hout (s : S) : x * (s.val : G) ∉ H :=
        fun h => hx ((H.mul_mem_cancel_right s.val.2).mp h)
      simp [walk_apply, w, hx, hout]
  · exact funext fun g => by simpa [w, g.property] using congrFun h (g : G)

private theorem integral_walk {K G : Type} [Group K] [Finite K] [Group G]
    (φ : K →* G) (S : Set K) [Fintype S] (hinv : ∀ s ∈ S, s ^ 2 = 1 ∧ s ≠ 1)
    (hn : ∀ s ∈ S, ∀ g : K, g * s * g⁻¹ ∈ S) {μ : ℂ} (hμ : (walk φ S).HasEigenvalue μ) :
    ∃ k : ℤ, (k : ℂ) = μ := by
  classical
  let := Fintype.ofFinite K
  apply hasIntegralSpectrum_adjMatrix_mulCayley_of_involutions S hinv hn μ
  rw [← Matrix.charpoly_toLin', ← hasEigenvalue_iff_isRoot_charpoly, cayley_walk]
  · exact eigenvalue_walk_pullback φ S hμ
  · exact fun hs => (hinv 1 hs).2 rfl
  · have hself (s : K) (hs : s ∈ S) : s⁻¹ = s :=
      inv_eq_of_mul_eq_one_right (by simpa [sq] using (hinv s hs).1)
    intro g
    constructor
    · intro h
      rwa [← inv_inv g, hself g⁻¹ h]
    · intro h
      rwa [hself g h]

-- A common eigenvector for b and a - b gives the eigenvalues of the difference.
private theorem integral_sub {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a b : Module.End ℂ V) (hc : Commute a b)
    (ha : ∀ μ, a.HasEigenvalue μ → ∃ k : ℤ, (k : ℂ) = μ)
    (hb : ∀ μ, b.HasEigenvalue μ → ∃ k : ℤ, (k : ℂ) = μ)
    {μ : ℂ} (hμ : (a - b).HasEigenvalue μ) : ∃ k : ℤ, (k : ℂ) = μ := by
  let E := (a - b).eigenspace μ
  have hm : ∀ v ∈ E, b v ∈ E :=
    mapsTo_genEigenspace_of_comm (hc.sub_left (Commute.refl b)) μ 1
  let : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hμ
  obtain ⟨β, hβ⟩ := exists_eigenvalue (b.restrict hm)
  obtain ⟨v, hv⟩ := hβ.exists_hasEigenvector
  have hv0 : (v : V) ≠ 0 := fun h => hv.2 (Subtype.ext h)
  have hbv : b v = β • (v : V) := congrArg Subtype.val hv.apply_eq_smul
  have hav : a v = (μ + β) • (v : V) := by
    rw [add_smul, ← hbv, ← sub_eq_iff_eq_add]
    exact mem_eigenspace_iff.mp v.2
  obtain ⟨j, hj⟩ := ha _ (hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.mpr hav, hv0⟩)
  obtain ⟨k, hk⟩ := hb _ (hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.mpr hbv, hv0⟩)
  exact ⟨j - k, by simp [hj, hk]⟩

open Equiv Equiv.Perm

private theorem swap_conj {n : ℕ} {s : Perm (Fin n)} (hs : s.IsSwap) (g : Perm (Fin n)) :
    (g * s * g⁻¹).IsSwap := by
  obtain ⟨x, y, hxy, rfl⟩ := hs
  exact ⟨g x, g y, g.injective.ne hxy, (Equiv.swap_apply_apply g x y).symm⟩

-- This applies both to all transpositions and to the transpositions in a centralizer.
private theorem integral_swaps {n : ℕ} {K : Type} [Group K] [Finite K]
    (φ : K →* Perm (Fin n)) (hφ : Function.Injective φ)
    [Fintype {s : K // (φ s).IsSwap}] {μ : ℂ}
    (hμ : (walk φ {s | (φ s).IsSwap}).HasEigenvalue μ) : ∃ k : ℤ, (k : ℂ) = μ := by
  apply integral_walk φ _ _ _ hμ
  · intro s hs
    obtain ⟨x, y, hxy, h⟩ := hs
    refine ⟨hφ (by simp [h, sq]), fun he => hxy ?_⟩
    have heq : (1 : Perm (Fin n)) = swap x y := by simpa [he] using h
    simpa using congrArg (· x) heq
  · intro s hs g
    change (φ (g * s * g⁻¹)).IsSwap
    simpa only [map_mul, map_inv] using swap_conj hs (φ g)

private theorem swapSum_commutes {n : ℕ} (g : Perm (Fin n))
    [Fintype {s : Perm (Fin n) // s.IsSwap}] :
    Commute (walk (MonoidHom.id _) {s : Perm (Fin n) | s.IsSwap})
      (rightRegular (k := ℂ) g) := by
  let e := Equiv.subtypeEquiv (MulAut.conj g).toEquiv (p := Perm.IsSwap) (q := Perm.IsSwap)
    (fun s => ⟨fun h => swap_conj h g, fun h => by
      simpa [MulAut.conj_apply, mul_assoc] using swap_conj h g⁻¹⟩)
  rw [Commute, SemiconjBy, walk, Finset.sum_mul, Finset.mul_sum]
  symm
  apply Fintype.sum_equiv e
  intro s
  simp only [MonoidHom.id_apply, ← map_mul]
  congr 1
  change g * s.val = (g * s.val * g⁻¹) * g
  simp

-- Multiplying a noncommuting transposition by (a b) produces one of the two orientations.
private theorem crossing_swap_iff {n : ℕ} (a b : Fin n) (ha : a.val = 0) (hb : b.val = 1)
    (s : Perm (Fin n)) :
    s.IsSwap ∧ ¬ Commute s (swap a b) ↔
      ∃ k : Fin n, 2 ≤ k.val ∧ (s = swap a k ∨ s = swap b k) := by
  have hab : a ≠ b := fun h => by omega
  have third {k : Fin n} (hka : k ≠ a) (hkb : k ≠ b) : 2 ≤ k.val := by
    have := Fin.val_ne_of_ne hka
    have := Fin.val_ne_of_ne hkb
    omega
  constructor
  · rintro ⟨⟨x, y, hxy, rfl⟩, hn⟩
    have hshare : x = a ∨ x = b ∨ y = a ∨ y = b := by
      by_contra! h
      exact hn (disjoint_swap_swap (by simp [hxy, hab, h])).commute
    have hdiff : swap x y ≠ swap a b := fun he => hn (he ▸ Commute.refl _)
    rcases hshare with rfl | rfl | rfl | rfl
    · exact ⟨y, third hxy.symm (fun h => hdiff (h ▸ rfl)), Or.inl rfl⟩
    · exact ⟨y, third (fun h => hdiff (h ▸ swap_comm _ _)) hxy.symm, Or.inr rfl⟩
    · exact ⟨x, third hxy (fun h => hdiff (h ▸ swap_comm _ _)), Or.inl (swap_comm _ _)⟩
    · exact ⟨x, third (fun h => hdiff (h ▸ rfl)) hxy, Or.inr (swap_comm _ _)⟩
  · rintro ⟨k, hk, h⟩
    have hka : k ≠ a := fun h => by subst k; omega
    have hkb : k ≠ b := fun h => by subst k; omega
    rcases h with rfl | rfl
    · refine ⟨⟨a, k, hka.symm, rfl⟩, fun hc => ?_⟩
      have := congrArg (fun f : Perm (Fin n) => f k) hc.eq
      simp [mul_apply, swap_apply_of_ne_of_ne hka hkb, hab] at this
    · refine ⟨⟨b, k, hkb.symm, rfl⟩, fun hc => ?_⟩
      have := congrArg (fun f : Perm (Fin n) => f k) hc.eq
      simp [mul_apply, swap_apply_of_ne_of_ne hka hkb, hab.symm] at this

private theorem threeCycle_or_inv_iff {n : ℕ} (a b : Fin n) (ha : a.val = 0) (hb : b.val = 1)
    (s : Perm (Fin n)) :
    (swap a b * s ∈ threeCyclesOneTwo n ∨ (swap a b * s)⁻¹ ∈ threeCyclesOneTwo n) ↔
      s.IsSwap ∧ ¬ Commute s (swap a b) := by
  have hmem (g : Perm (Fin n)) : g ∈ threeCyclesOneTwo n ↔
      ∃ k : Fin n, 2 ≤ k.val ∧ g = swap a b * swap b k := by
    constructor
    · rintro ⟨x, y, k, hx, hy, hk, he⟩
      obtain rfl : x = a := Fin.ext (hx.trans ha.symm)
      obtain rfl : y = b := Fin.ext (hy.trans hb.symm)
      exact ⟨k, hk, he⟩
    · rintro ⟨k, hk, he⟩
      exact ⟨a, b, k, ha, hb, hk, he⟩
  have hinv (k : Fin n) (hk : 2 ≤ k.val) :
      (swap a b * swap b k)⁻¹ = swap a b * swap a k := by
    have hka : k ≠ a := fun h => by subst k; omega
    have hkb : k ≠ b := fun h => by subst k; omega
    rw [mul_inv_rev, swap_inv, swap_inv, mul_swap_eq_swap_mul (swap a b) a k,
      swap_apply_left, swap_apply_of_ne_of_ne hka hkb]
  rw [crossing_swap_iff a b ha hb, hmem, hmem]
  simp only [inv_eq_iff_eq_inv, mul_right_inj]
  constructor
  · rintro (⟨k, hk, h⟩ | ⟨k, hk, h⟩)
    · exact ⟨k, hk, Or.inr h⟩
    · rw [hinv k hk] at h
      exact ⟨k, hk, Or.inl (mul_left_cancel h)⟩
  · rintro ⟨k, hk, rfl | rfl⟩
    · exact Or.inr ⟨k, hk, (hinv k hk).symm⟩
    · exact Or.inl ⟨k, hk, rfl⟩

open Classical in
private theorem integral_crossing {n : ℕ} (t : Perm (Fin n)) (ht : t ^ 2 = 1) {μ : ℂ}
    (hμ : HasEigenvalue (rightRegular (k := ℂ) t *
      walk (MonoidHom.id _) {s : Perm (Fin n) | s.IsSwap ∧ ¬ Commute s t}) μ) :
    ∃ k : ℤ, (k : ℂ) = μ := by
  classical
  let G := Perm (Fin n)
  let H : Subgroup G := Subgroup.centralizer {t}
  let A := walk (MonoidHom.id G) {s : G | s.IsSwap}
  let B := walk H.subtype {s : H | (s.val : G).IsSwap}
  let D := walk (MonoidHom.id G) {s : G | s.IsSwap ∧ ¬ Commute s t}
  let T := rightRegular (k := ℂ) t
  have hH (s : G) : s ∈ H ↔ Commute s t := Subgroup.mem_centralizer_singleton_iff
  have hsplit : B + D = A := by
    let W := {s : G // s.IsSwap}
    let p (s : W) := Commute s.val t
    let e : {s : H // (s.val : G).IsSwap} ≃ {s : W // p s} :=
      { toFun s := ⟨⟨s.val.val, s.prop⟩, (hH _).mp s.val.prop⟩
        invFun s := ⟨⟨s.val.val, (hH _).mpr s.prop⟩, s.val.prop⟩
        left_inv _ := rfl
        right_inv _ := rfl }
    let e' : {s : G // s.IsSwap ∧ ¬ Commute s t} ≃ {s : W // ¬ p s} :=
      { toFun s := ⟨⟨s.val, s.prop.1⟩, s.prop.2⟩
        invFun s := ⟨s.val.val, s.val.prop, s.prop⟩
        left_inv _ := rfl
        right_inv _ := rfl }
    unfold A B D walk
    convert Fintype.sum_subtype_add_sum_subtype p (fun s => rightRegular (k := ℂ) s.val) using 1
    congr 1
    · exact Fintype.sum_equiv e _ _ fun _ => rfl
    · exact Fintype.sum_equiv e' _ _ fun _ => rfl
  have hD : D = A - B := eq_sub_of_add_eq (add_comm B D ▸ hsplit)
  have hAB : Commute A B :=
    Commute.sum_right _ _ _ fun s _ => swapSum_commutes (s.val : G)
  have hTB : Commute T B := Commute.sum_right _ _ _ fun s _ =>
    ((hH _).mp s.val.property).symm.map rightRegular
  have hTD : Commute T D := hD ▸ (swapSum_commutes t).symm.sub_right hTB
  have hT : T ^ 2 = 1 := by
    change rightRegular (k := ℂ) t ^ 2 = 1
    rw [← map_pow, ht, map_one]
  -- Squaring removes the commuting involution T, hence only the sign of an eigenvalue changes.
  have hs := (hμ.pow 2).mem_spectrum
  change μ ^ 2 ∈ spectrum ℂ ((T * D) ^ 2) at hs
  rw [hTD.mul_pow, hT, one_mul, spectrum.map_pow_of_pos _ (by decide : 0 < 2)] at hs
  obtain ⟨ν, hν, he⟩ := hs
  have hνD := hasEigenvalue_iff_mem_spectrum.mpr hν
  rw [hD] at hνD
  obtain ⟨k, hk⟩ := integral_sub A B hAB
    (fun _ h => integral_swaps (MonoidHom.id G) Function.injective_id h)
    (fun _ h => integral_swaps H.subtype Subtype.val_injective h) hνD
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
  · exact ⟨k, hk.trans h⟩
  · exact ⟨-k, by simp [hk, h]⟩

/--
**The 3-cycle Cayley graph of the alternating group is integral.** For every $n \ge 3$, let $S$ be
the set of $3$-cycles $(1\,2\,k)$ with $3 \le k \le n$ in the alternating group $A_n$, and let
$R = S \cup S^{-1}$. Then the Cayley graph $\mathrm{Cay}(A_n, R)$, whose vertices are the elements
of $A_n$ with distinct $x$ and $y$ adjacent when $x^{-1} y \in R$ or $y^{-1} x \in R$, is
integral: every eigenvalue of its integer adjacency matrix (every complex root of the
characteristic polynomial of that matrix) is an integer.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.50 (D. V.
Lytkina); resolution: (a) D. O. Revin, letter of 21 April 2018; A. Abdollahi, letter of 3 May 2018;
(b) W. Guo, D. V. Lytkina, V. D. Mazurov and D. O. Revin, Integral Cayley graphs, Algebra Logic 58
(2019), no. 4, 297-305, doi:10.1007/s10469-019-09550-2, Kourovka Archive, Problem 19.50: (a) Yes,
with a character-theoretic proof in the Archive (each eigenvalue is (1/χ(1)) ∑_{r ∈ R} χ(r),
rational since characters take integer values on involutions); (b) Yes,
https://arxiv.org/abs/1401.0300v49.
-/
theorem alternatingThreeCycleCayleyGraphIntegral_holds :
    alternatingThreeCycleCayleyGraphIntegral := by
  classical
  intro n hn μ hμ
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let t := swap a b
  let H := alternatingGroup (Fin n)
  let R : Set H := {g | g.val ∈ threeCyclesOneTwo n ∨ g.val⁻¹ ∈ threeCyclesOneTwo n}
  let S : Set (Perm (Fin n)) := {s | s.IsSwap ∧ ¬ Commute s t}
  have ht (s : Perm (Fin n)) : t * (t * s) = s := swap_mul_self_mul a b s
  have hgen := threeCycle_or_inv_iff a b rfl rfl
  have h1 : 1 ∉ R := by
    intro h
    have he := (hgen t).mp (by simpa [t, swap_mul_self, R] using h)
    exact he.2 (Commute.refl t)
  have hi (g : H) : g⁻¹ ∈ R ↔ g ∈ R := by simp [R, or_comm]
  change (((SimpleGraph.mulCayley R).adjMatrix ℤ).map (Int.castRingHom ℂ)).charpoly.IsRoot μ at hμ
  rw [← Matrix.charpoly_toLin', ← hasEigenvalue_iff_isRoot_charpoly, cayley_walk R h1 hi] at hμ
  have he := eigenvalue_walk_extend H R hμ
  -- Multiplication by t bijects the crossing transpositions with the graph's generators.
  have htSwap : t.IsSwap := ⟨a, b, (Fin.ne_of_val_ne (by decide : 0 ≠ 1)), rfl⟩
  let e : S ≃ R :=
    { toFun s := ⟨⟨t * s.val, mul_mem_alternatingGroup_of_isSwap htSwap s.prop.1⟩,
        (hgen s.val).mpr s.prop⟩
      invFun r := ⟨t * r.val.val, (hgen _).mp (by rw [ht]; exact r.prop)⟩
      left_inv s := Subtype.ext (ht s.val)
      right_inv r := Subtype.ext (Subtype.ext (ht r.val.val)) }
  apply integral_crossing t (by simp [t, sq])
  suffices rightRegular (k := ℂ) t * walk (MonoidHom.id _) S = walk H.subtype R by rwa [this]
  unfold walk
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv e _ _ fun s => (map_mul rightRegular t s.val).symm

end MathlibExt.GroupTheory.IntegralCayleyGraphsKourovka19Problem50Wanted
