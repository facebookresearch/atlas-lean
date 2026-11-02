/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Matrix.Block

import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Jordan normal form

This file proves that a finite square matrix over a field has a Jordan normal form whenever its
characteristic polynomial splits.  The proof first constructs Jordan-chain bases for nilpotent
endomorphisms, then applies that construction on the maximal generalized eigenspaces.
-/

@[expose] public section

open Module
open scoped BigOperators

universe v

variable {K : Type*} [Field K]

namespace MathlibExt.LinearAlgebra.Matrix.JordanNormalFormWanted

/--
**Jordan block.** For a natural number $s$ and a scalar $\mu$ in a field $K$, the Jordan block of
size $s$ with eigenvalue $\mu$ is the $s \times s$ matrix over $K$, with rows and columns indexed
by $\{0, \dots, s-1\}$, whose $(i, j)$ entry is $1$ if $j = i + 1$, $\mu$ if $i = j$, and $0$
otherwise: it has $\mu$ on the diagonal, $1$ on the first superdiagonal and $0$ elsewhere.

Sources: Mathlib `docs/undergrad.yaml`, Linear algebra / Structure theory of endomorphisms /
Jordan normal form; R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University
Press (2013), Section 3.4.
-/
def jordanBlock (s : ℕ) (μ : K) : Matrix (Fin s) (Fin s) K :=
  fun i j => if i.val + 1 = j.val then 1 else if i = j then μ else 0

/--
**Entries of a Jordan block.** For a natural number $s$, a scalar $\mu$ in a field $K$ and indices
$i, j \in \{0, \dots, s-1\}$, the $(i, j)$ entry of the Jordan block of size $s$ with eigenvalue
$\mu$ is $1$ if $j = i + 1$, is $\mu$ if $i = j$, and is $0$ otherwise.

Sources: Mathlib `docs/undergrad.yaml`, Linear algebra / Structure theory of endomorphisms /
Jordan normal form; https://en.wikipedia.org/wiki/Jordan_normal_form.
-/
theorem jordanBlock_apply (s : ℕ) (μ : K) (i j : Fin s) :
    jordanBlock s μ i j = (if i.val + 1 = j.val then 1 else if i = j then μ else 0) := rfl

end MathlibExt.LinearAlgebra.Matrix.JordanNormalFormWanted

open MathlibExt.LinearAlgebra.Matrix.JordanNormalFormWanted

namespace LinearMap

/-- **Matrix of an endomorphism on a Jordan chain.** Let $V$ be a vector space over a field $K$,
let $f$ be a linear endomorphism of $V$, let $\mu \in K$, and let $b_0, \dots, b_d$ be a basis of
$V$ such that $f(b_0) = \mu b_0$ and $f(b_{j+1}) = \mu b_{j+1} + b_j$ for every $j < d$. Then the
matrix of $f$ with respect to the basis $(b_0, \dots, b_d)$ is the Jordan block of size $d + 1$
with eigenvalue $\mu$. -/
theorem toMatrix_eq_jordanBlock
    {V : Type*} [AddCommGroup V] [Module K V]
    (d : ℕ) (b : Basis (Fin (d + 1)) K V) (f : Module.End K V) (μ : K)
    (hzero : f (b 0) = μ • b 0)
    (hsucc : ∀ j : Fin d, f (b j.succ) = μ • b j.succ + b j.castSucc) :
    LinearMap.toMatrix b b f = jordanBlock (d + 1) μ := by
  ext i j
  refine Fin.cases ?_ (fun q => ?_) j
  · rw [LinearMap.toMatrix_apply, hzero]
    by_cases hi : i = 0
    · subst i
      simp [jordanBlock]
    · simp [jordanBlock, hi]
  · rw [LinearMap.toMatrix_apply, hsucc]
    have hne : q.succ ≠ q.castSucc := by
      intro hq
      have := congrArg Fin.val hq
      simp at this
    by_cases hp : i = q.castSucc
    · subst i
      simp [jordanBlock, hne.symm]
    by_cases hd : i = q.succ
    · subst i
      simp [jordanBlock, hne]
    have hpval : i.val ≠ q.val := fun h => hp (Fin.ext h)
    simp [jordanBlock, hp, hd, hpval]

/-- **Matrix of an endomorphism on a basis of Jordan chains.** Let $V$ be a vector space over a
field $K$, let $f$ be a linear endomorphism of $V$, and let $\iota$ be a finite set. For each
$i \in \iota$ let $d_i \in \mathbb{N}$ and $\mu_i \in K$, and let $(b_{i,r})$, indexed by
$i \in \iota$ and $0 \le r \le d_i$, be a basis of $V$ such that $f(b_{i,0}) = \mu_i b_{i,0}$ and
$f(b_{i,j+1}) = \mu_i b_{i,j+1} + b_{i,j}$ for every $i \in \iota$ and every $j < d_i$. Then the
matrix of $f$ with respect to $b$ is the block-diagonal matrix whose $i$-th diagonal block is the
Jordan block of size $d_i + 1$ with eigenvalue $\mu_i$. -/
theorem toMatrix_eq_blockDiagonal_jordanBlock
    {V ι : Type*} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (d : ι → ℕ) (b : Basis (Σ i, Fin (d i + 1)) K V) (f : Module.End K V) (μ : ι → K)
    (hzero : ∀ i, f (b ⟨i, 0⟩) = μ i • b ⟨i, 0⟩)
    (hsucc : ∀ i (j : Fin (d i)),
      f (b ⟨i, j.succ⟩) = μ i • b ⟨i, j.succ⟩ + b ⟨i, j.castSucc⟩) :
    LinearMap.toMatrix b b f =
      Matrix.blockDiagonal' (fun i ↦ jordanBlock (d i + 1) (μ i)) := by
  classical
  ext ⟨i, r⟩ ⟨j, q⟩
  refine Fin.cases ?_ (fun t ↦ ?_) q
  · rw [LinearMap.toMatrix_apply, hzero]
    by_cases hij : i = j
    · subst j
      by_cases hr : r = 0
      · subst r
        simp [Matrix.blockDiagonal'_apply_eq, jordanBlock]
      · simp [Matrix.blockDiagonal'_apply_eq, jordanBlock, hr]
    · simp [Matrix.blockDiagonal'_apply, hij]
  · rw [LinearMap.toMatrix_apply, hsucc]
    by_cases hij : i = j
    · subst j
      have hne : t.succ ≠ t.castSucc := by
        intro ht
        have := congrArg Fin.val ht
        simp at this
      by_cases hp : r = t.castSucc
      · subst r
        simp [Matrix.blockDiagonal'_apply_eq, jordanBlock, hne.symm]
      by_cases hd : r = t.succ
      · subst r
        simp [Matrix.blockDiagonal'_apply_eq, jordanBlock, hne]
      have hpval : r.val ≠ t.val := fun h ↦ hp (Fin.ext h)
      simp [Matrix.blockDiagonal'_apply_eq, jordanBlock, hp, hd, hpval]
    · simp [Matrix.blockDiagonal'_apply, hij]

end LinearMap

private def jordanRangeMap
    {V : Type*} [AddCommGroup V] [Module K V] (f : Module.End K V) :
    V →ₗ[K] f.range :=
  f.codRestrict f.range fun x => ⟨x, rfl⟩

private noncomputable def jordanRangePreimage
    {V : Type*} [AddCommGroup V] [Module K V] (f : Module.End K V) (x : f.range) : V :=
  Classical.choose x.property

private theorem jordanRangePreimage_spec
    {V : Type*} [AddCommGroup V] [Module K V] (f : Module.End K V) (x : f.range) :
    f (jordanRangePreimage f x) = x :=
  Classical.choose_spec x.property

private noncomputable def jordanLiftedChains
    {V ι : Type*} [AddCommGroup V] [Module K V] (f : Module.End K V)
    (d : ι → ℕ) (b : Basis (Σ i, Fin (d i + 1)) K f.range) :
    (Σ i, Fin (d i + 1 + 1)) → V :=
  fun p => Fin.lastCases
    (jordanRangePreimage f (b ⟨p.1, Fin.last (d p.1)⟩))
    (fun q => (b ⟨p.1, q⟩ : f.range).1) p.2

private def jordanAugmentEquiv {ι J : Type*} (d : ι → ℕ) :
    ((Σ i, Fin (d i + 1 + 1)) ⊕ J) ≃
      (Σ q : ι ⊕ J, Fin (Sum.elim (fun i => d i + 1) (fun _ => 0) q + 1)) where
  toFun
    | Sum.inl p => ⟨Sum.inl p.1, p.2⟩
    | Sum.inr j => ⟨Sum.inr j, 0⟩
  invFun
    | ⟨Sum.inl i, j⟩ => Sum.inl ⟨i, j⟩
    | ⟨Sum.inr j, _⟩ => Sum.inr j
  left_inv x := by cases x <;> rfl
  right_inv x := by
    obtain ⟨i, j⟩ := x
    cases i with
    | inl i => rfl
    | inr i =>
      change (⟨Sum.inr i, (0 : Fin 1)⟩ :
        Σ q : ι ⊕ J, Fin (Sum.elim (fun i => d i + 1) (fun _ => 0) q + 1)) =
          ⟨Sum.inr i, j⟩
      congr
      apply Fin.ext
      omega

private theorem jordan_sumExtend_inl
    {V ι : Type*} [AddCommGroup V] [Module K V]
    (c : ι → V) (hc : LinearIndependent K c) (i : ι) :
    Basis.sumExtend hc (Sum.inl i) = c i := by
  simp [Basis.sumExtend]
  rfl

private theorem jordan_liftedChains_linearIndependent
    {V W ι : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [Finite ι] (d : ι → ℕ) (b : Basis (Σ i, Fin (d i + 1)) K W)
    (F : V →ₗ[K] W) (E : W →ₗ[K] V) (hE : E.ker = ⊥)
    (c : (Σ i, Fin (d i + 1 + 1)) → V)
    (hc0 : ∀ i, F (c ⟨i, 0⟩) = 0)
    (hcs : ∀ i (j : Fin (d i + 1)), F (c ⟨i, j.succ⟩) = b ⟨i, j⟩)
    (hc0' : ∀ i, c ⟨i, 0⟩ = E (b ⟨i, 0⟩)) :
    LinearIndependent K c := by
  let _ := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have hFa : ∑ p, a p • F (c p) = 0 := calc
    _ = F (∑ p, a p • c p) := by simp
    _ = 0 := by rw [ha, map_zero]
  have himage : ∑ p : Σ i, Fin (d i + 1), a ⟨p.1, p.2.succ⟩ • b p = 0 := by
    rw [Fintype.sum_sigma] at hFa ⊢
    simpa only [Fin.sum_univ_succ, hc0, hcs, smul_zero, zero_add] using hFa
  have hsucc := (Fintype.linearIndependent_iff.mp b.linearIndependent)
    (fun p => a ⟨p.1, p.2.succ⟩) himage
  have hsucc' : ∀ i (j : Fin (d i + 1)), a ⟨i, j.succ⟩ = 0 :=
    fun i j => hsucc ⟨i, j⟩
  have hbottom : ∑ i, a ⟨i, 0⟩ • E (b ⟨i, 0⟩) = 0 := by
    rw [Fintype.sum_sigma] at ha
    calc
      _ = ∑ i, ∑ j, a ⟨i, j⟩ • c ⟨i, j⟩ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Fin.sum_univ_succ, hc0']
        simp [hsucc']
      _ = 0 := ha
  have hbottomLI : LinearIndependent K (fun i => E (b ⟨i, 0⟩)) :=
    (b.linearIndependent.comp (fun i => ⟨i, 0⟩) (by
      intro i j h
      exact (Sigma.ext_iff.mp h).1)).map' E hE
  have hzero := (Fintype.linearIndependent_iff.mp hbottomLI)
    (fun i => a ⟨i, 0⟩) hbottom
  rintro ⟨i, j⟩
  refine Fin.cases (hzero i) (fun q => ?_) j
  simpa using hsucc' i q

private theorem jordan_nilpotentRangeStep
    {V ι : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Finite ι]
    (f : Module.End K V) (d : ι → ℕ)
    (b : Basis (Σ i, Fin (d i + 1)) K f.range)
    (hmap : Set.MapsTo f f.range f.range)
    (hz : ∀ i, (f.restrict hmap) (b ⟨i, 0⟩) = 0)
    (hs : ∀ i (j : Fin (d i)),
      (f.restrict hmap) (b ⟨i, j.succ⟩) = b ⟨i, j.castSucc⟩) :
    ∃ (ι' : Type v) (_ : Fintype ι') (d' : ι' → ℕ)
      (b' : Basis (Σ i, Fin (d' i + 1)) K V),
      (∀ i, f (b' ⟨i, 0⟩) = 0) ∧
        ∀ i (j : Fin (d' i)), f (b' ⟨i, j.succ⟩) = b' ⟨i, j.castSucc⟩ := by
  let _ := Fintype.ofFinite ι
  let c := jordanLiftedChains f d b
  have hc0 : ∀ i, jordanRangeMap f (c ⟨i, 0⟩) = 0 := by
    intro i
    have h0 : (0 : Fin (d i + 1 + 1)) = (0 : Fin (d i + 1)).castSucc := by rfl
    rw [h0]
    simp only [c, jordanLiftedChains, Fin.lastCases_castSucc]
    exact hz i
  have hcs : ∀ i (j : Fin (d i + 1)),
      jordanRangeMap f (c ⟨i, j.succ⟩) = b ⟨i, j⟩ := by
    intro i j
    refine Fin.lastCases ?_ (fun q => ?_) j
    · rw [Fin.succ_last]
      simp only [Nat.succ_eq_add_one, c, jordanLiftedChains, Fin.lastCases_last]
      apply Subtype.ext
      exact jordanRangePreimage_spec f (b ⟨i, Fin.last (d i)⟩)
    · rw [Fin.succ_castSucc]
      simp only [c, jordanLiftedChains, Fin.lastCases_castSucc]
      exact hs i q
  have hc0' : ∀ i, c ⟨i, 0⟩ = f.range.subtype (b ⟨i, 0⟩) := by
    intro i
    have h0 : (0 : Fin (d i + 1 + 1)) = (0 : Fin (d i + 1)).castSucc := by rfl
    rw [h0]
    simp only [c, jordanLiftedChains, Fin.lastCases_castSucc]
    rfl
  have hc : LinearIndependent K c :=
    jordan_liftedChains_linearIndependent d b (jordanRangeMap f) f.range.subtype
      (by simp) c hc0 hcs hc0'
  let B := Basis.sumExtend hc
  let J := Basis.sumExtendIndex hc
  let g : f.range →ₗ[K] V := b.constr K fun p => c ⟨p.1, p.2.succ⟩
  have hFg : jordanRangeMap f ∘ₗ g = LinearMap.id := by
    apply b.ext
    intro p
    rw [LinearMap.comp_apply]
    change jordanRangeMap f ((b.constr K fun p => c ⟨p.1, p.2.succ⟩) (b p)) = _
    rw [Basis.constr_basis]
    exact hcs p.1 p.2
  let w : ((Σ i, Fin (d i + 1 + 1)) ⊕ J) → V := fun q =>
    match q with
    | Sum.inl p => c p
    | Sum.inr j => B (Sum.inr j) - g (jordanRangeMap f (B (Sum.inr j)))
  have hgmem (x : f.range) : g x ∈ Submodule.span K (Set.range c) := by
    rw [← b.sum_repr x]
    simp only [map_sum, map_smul, g, Basis.constr_basis]
    exact Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span
        (Set.mem_range_self (⟨p.1, p.2.succ⟩ : Σ i, Fin (d i + 1 + 1))))
  have hcspan : Submodule.span K (Set.range c) ≤ Submodule.span K (Set.range w) :=
    Submodule.span_mono <| by
      rintro _ ⟨p, rfl⟩
      exact Set.mem_range_self (Sum.inl p)
  have hwspan : ⊤ ≤ Submodule.span K (Set.range w) := by
    rw [← B.span_eq]
    apply Submodule.span_le.2
    rintro _ ⟨q, rfl⟩
    cases q with
    | inl p =>
      rw [jordan_sumExtend_inl c hc p]
      exact Submodule.subset_span (Set.mem_range_self (Sum.inl p))
    | inr j =>
      rw [show B (Sum.inr j) =
        w (Sum.inr j) + g (jordanRangeMap f (B (Sum.inr j))) by simp [w]]
      exact Submodule.add_mem _ (Submodule.subset_span (Set.mem_range_self (Sum.inr j)))
        (hcspan (hgmem _))
  let _ : Finite ((Σ i, Fin (d i + 1 + 1)) ⊕ J) := Module.Finite.finite_basis B
  let _ : Finite J := Finite.of_injective
    (fun j : J => (Sum.inr j : (Σ i, Fin (d i + 1 + 1)) ⊕ J)) Sum.inr_injective
  let _ := Fintype.ofFinite J
  let D := basisOfTopLeSpanOfCardEqFinrank w hwspan
    (Module.finrank_eq_card_basis B).symm
  have hwker (j : J) : f (w (Sum.inr j)) = 0 := by
    change f (B (Sum.inr j) - g (jordanRangeMap f (B (Sum.inr j)))) = 0
    have hh := DFunLike.congr_fun hFg (jordanRangeMap f (B (Sum.inr j)))
    have hh' : f (g (jordanRangeMap f (B (Sum.inr j)))) = f (B (Sum.inr j)) := by
      have hh' := congrArg Subtype.val hh
      change f (g (jordanRangeMap f (B (Sum.inr j)))) = f (B (Sum.inr j)) at hh'
      exact hh'
    rw [map_sub, hh']
    simp
  let d' : ι ⊕ J → ℕ := Sum.elim (fun i => d i + 1) (fun _ => 0)
  let e := jordanAugmentEquiv (J := J) d
  let b' := D.reindex e
  have hc0V : ∀ i, f (c ⟨i, 0⟩) = 0 := by
    intro i
    have hi := congrArg Subtype.val (hc0 i)
    change f (c ⟨i, 0⟩) = 0 at hi
    exact hi
  have hcsV : ∀ i (q : Fin (d i + 1)), f (c ⟨i, q.succ⟩) = c ⟨i, q.castSucc⟩ := by
    intro i q
    have hi := congrArg Subtype.val (hcs i q)
    change f (c ⟨i, q.succ⟩) = (b ⟨i, q⟩ : f.range).1 at hi
    simpa only [c, jordanLiftedChains, Fin.lastCases_castSucc] using hi
  refine ⟨ι ⊕ J, inferInstance, d', b', ?_, ?_⟩
  · rintro (i | j)
    · simp only [b', d', e, D, w, Basis.reindex_apply, jordanAugmentEquiv,
        coe_basisOfTopLeSpanOfCardEqFinrank]
      convert hc0V i using 1
      rfl
    · simpa [b', d', e, D, w, Basis.reindex_apply, jordanAugmentEquiv] using hwker j
  · rintro (i | j) q
    · simpa [b', d', e, D, w, Basis.reindex_apply, jordanAugmentEquiv] using hcsV i q
    · exact Fin.elim0 q

private theorem jordan_exists_chainBasis_of_isNilpotent_aux
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (hf : IsNilpotent f) :
    ∃ (ι : Type v) (_ : Fintype ι) (d : ι → ℕ)
      (b : Basis (Σ i, Fin (d i + 1)) K V),
      (∀ i, f (b ⟨i, 0⟩) = 0) ∧
        ∀ i (j : Fin (d i)), f (b ⟨i, j.succ⟩) = b ⟨i, j.castSucc⟩ := by
  induction hn : finrank K V using Nat.strong_induction_on generalizing V with
  | h n ih =>
      by_cases hn0 : n = 0
      · have hzero : finrank K V = 0 := hn.trans hn0
        have _ : Subsingleton V := Module.finrank_zero_iff.mp hzero
        let ι := PEmpty
        let d : ι → ℕ := PEmpty.elim
        let b : Basis (Σ i, Fin (d i + 1)) K V := Basis.empty V
        refine ⟨ι, inferInstance, d, b, ?_, ?_⟩
        · intro i
          exact i.elim
        · intro i
          exact i.elim
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        let _ : Nontrivial V := Module.nontrivial_of_finrank_pos (hn.symm ▸ hnpos)
        have hmap : Set.MapsTo f f.range f.range := by
          rintro _ ⟨x, rfl⟩
          exact ⟨f x, rfl⟩
        have hrange : f.range ≠ ⊤ := by
          intro htop
          exact hf.not_isUnit ((LinearMap.isUnit_iff_range_eq_top f).2 htop)
        have hrank : finrank K f.range < n := by
          rw [← hn]
          exact Submodule.finrank_lt hrange
        have hfr : IsNilpotent (f.restrict hmap) :=
          Module.End.isNilpotent.restrict hmap hf
        obtain ⟨ι, hι, d, b, hz, hs⟩ :=
          ih (finrank K f.range) hrank (f.restrict hmap) hfr rfl
        let _ : Fintype ι := hι
        exact jordan_nilpotentRangeStep f d b hmap hz hs

namespace Module.End

/-- **Jordan chain basis for a nilpotent endomorphism.** Let $V$ be a finite-dimensional vector
space over a field $K$ and let $f$ be a nilpotent linear endomorphism of $V$. Then there are
$k \in \mathbb{N}$, natural numbers $d_0, \dots, d_{k-1}$ and a basis $(b_{i,r})$ of $V$, indexed
by $i < k$ and $0 \le r \le d_i$, such that $f(b_{i,0}) = 0$ and $f(b_{i,j+1}) = b_{i,j}$ for
every $i < k$ and every $j < d_i$, and such that the matrix of $f$ with respect to $b$ is the
block-diagonal matrix whose $i$-th diagonal block is the Jordan block of size $d_i + 1$ with
eigenvalue $0$. -/
theorem exists_jordanBasis_of_isNilpotent
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (hf : IsNilpotent f) :
    ∃ (k : ℕ) (d : Fin k → ℕ) (b : Basis (Σ i, Fin (d i + 1)) K V),
      (∀ i, f (b ⟨i, 0⟩) = 0) ∧
      (∀ i (j : Fin (d i)), f (b ⟨i, j.succ⟩) = b ⟨i, j.castSucc⟩) ∧
      LinearMap.toMatrix b b f =
        Matrix.blockDiagonal' (fun i ↦ jordanBlock (d i + 1) 0) := by
  classical
  obtain ⟨ι, hι, d, b, hzero, hsucc⟩ := jordan_exists_chainBasis_of_isNilpotent_aux f hf
  let _ : Fintype ι := hι
  let eι := Fintype.equivFin ι
  let d' : Fin (Fintype.card ι) → ℕ := fun i ↦ d (eι.symm i)
  let eσ : (Σ i, Fin (d i + 1)) ≃ (Σ i, Fin (d' i + 1)) :=
    Equiv.sigmaCongrLeft' eι
  let b' := b.reindex eσ
  have hzero' : ∀ i, f (b' ⟨i, 0⟩) = 0 := by
    intro i
    simpa [b', eσ, d', eι, Basis.reindex_apply, Equiv.sigmaCongrLeft'] using
      hzero (eι.symm i)
  have hsucc' : ∀ i (j : Fin (d' i)),
      f (b' ⟨i, j.succ⟩) = b' ⟨i, j.castSucc⟩ := by
    intro i j
    simpa [b', eσ, d', eι, Basis.reindex_apply, Equiv.sigmaCongrLeft'] using
      hsucc (eι.symm i) j
  refine ⟨Fintype.card ι, d', b', hzero', hsucc', ?_⟩
  exact LinearMap.toMatrix_eq_blockDiagonal_jordanBlock d' b' f (fun _ ↦ 0)
    (by simpa using hzero') (by simpa using hsucc')

private theorem jordan_isInternal_maxGenEigenspace_roots
    {V : Type v} [DecidableEq K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (hf : f.charpoly.Splits) :
    DirectSum.IsInternal
      (fun μ : f.charpoly.roots.toFinset ↦ f.maxGenEigenspace (μ : K)) := by
  classical
  let S := f.charpoly.roots.toFinset
  let A : S → Submodule K V := fun μ ↦ f.maxGenEigenspace (μ : K)
  have hind : iSupIndep A :=
    f.independent_maxGenEigenspace.comp Subtype.coe_injective
  have hfinrank : finrank K (↑(⨆ μ, A μ)) = ∑ μ, finrank K (A μ) := by
    calc
      finrank K (↑(⨆ μ, A μ)) =
          finrank K (LinearMap.range (DirectSum.coeLinearMap A)) := by
            rw [DirectSum.range_coeLinearMap]
      _ = finrank K (DirectSum S fun μ ↦ A μ) :=
        LinearMap.finrank_range_of_inj hind.dfinsupp_lsum_injective
      _ = ∑ μ, finrank K (A μ) := Module.finrank_directSum K (fun μ : S ↦ A μ)
  have hsum : ∑ μ : S, f.charpoly.rootMultiplicity (μ : K) = finrank K V := by
    calc
      ∑ μ : S, f.charpoly.rootMultiplicity (μ : K) =
          ∑ μ ∈ f.charpoly.roots.toFinset, f.charpoly.roots.count μ := by
            simpa only [S, Polynomial.count_roots] using
              (Finset.sum_subtype f.charpoly.roots.toFinset (fun _ ↦ Iff.rfl)
                (fun μ ↦ f.charpoly.rootMultiplicity μ)).symm
      _ = f.charpoly.roots.card := Multiset.toFinset_sum_count_eq _
      _ = f.charpoly.natDegree := hf.natDegree_eq_card_roots.symm
      _ = finrank K V := f.charpoly_natDegree
  have htop : ⨆ μ, A μ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hfinrank]
    simpa only [A, LinearMap.finrank_maxGenEigenspace_eq] using hsum
  simpa only [A, S] using
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop

/-- **Jordan chain basis for an endomorphism with split characteristic polynomial.** Let $V$ be
a finite-dimensional vector space over a field $K$ and let $f$ be a linear endomorphism of $V$
whose characteristic polynomial splits into linear factors over $K$. Then there are
$k \in \mathbb{N}$, natural numbers $d_0, \dots, d_{k-1}$, scalars $\mu_0, \dots, \mu_{k-1} \in K$
and a basis $(b_{i,r})$ of $V$, indexed by $i < k$ and $0 \le r \le d_i$, such that
$f(b_{i,0}) = \mu_i b_{i,0}$ and $f(b_{i,j+1}) = \mu_i b_{i,j+1} + b_{i,j}$ for every $i < k$ and
every $j < d_i$, and such that the matrix of $f$ with respect to $b$ is the block-diagonal matrix
whose $i$-th diagonal block is the Jordan block of size $d_i + 1$ with eigenvalue $\mu_i$. -/
theorem exists_jordanBasis_of_charpoly_splits
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (hf : f.charpoly.Splits) :
    ∃ (k : ℕ) (d : Fin k → ℕ) (μ : Fin k → K)
      (b : Basis (Σ i, Fin (d i + 1)) K V),
      (∀ i, f (b ⟨i, 0⟩) = μ i • b ⟨i, 0⟩) ∧
      (∀ i (j : Fin (d i)),
        f (b ⟨i, j.succ⟩) = μ i • b ⟨i, j.succ⟩ + b ⟨i, j.castSucc⟩) ∧
      LinearMap.toMatrix b b f =
        Matrix.blockDiagonal' (fun i ↦ jordanBlock (d i + 1) (μ i)) := by
  classical
  let S := f.charpoly.roots.toFinset
  let E : S → Submodule K V := fun a ↦ f.maxGenEigenspace (a : K)
  let hsub (a : S) : Set.MapsTo (f - algebraMap K (Module.End K V) (a : K)) (E a) (E a) :=
    f.mapsTo_maxGenEigenspace_of_comm
      (Algebra.mul_sub_algebraMap_commutes f (a : K)) (a : K)
  let N (a : S) : Module.End K (E a) :=
    (f - algebraMap K (Module.End K V) (a : K)).restrict (hsub a)
  have hnil (a : S) : IsNilpotent (N a) := by
    simpa only [N, E, hsub] using
      f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap (a : K) (hsub a)
  have hex (a : S) := exists_jordanBasis_of_isNilpotent (N a) (hnil a)
  choose k d b hb using hex
  have hzeroN (a : S) := (hb a).1
  have hsuccN (a : S) := (hb a).2.1
  have hzeroV (a : S) (i : Fin (k a)) :
      f (b a ⟨i, 0⟩ : E a) = (a : K) • (b a ⟨i, 0⟩ : E a) := by
    have h := congrArg Subtype.val (hzeroN a i)
    change f (b a ⟨i, 0⟩ : E a) - (a : K) • (b a ⟨i, 0⟩ : E a) = 0 at h
    exact sub_eq_zero.mp h
  have hsuccV (a : S) (i : Fin (k a)) (j : Fin (d a i)) :
      f (b a ⟨i, j.succ⟩ : E a) =
        (a : K) • (b a ⟨i, j.succ⟩ : E a) + (b a ⟨i, j.castSucc⟩ : E a) := by
    have h := congrArg Subtype.val (hsuccN a i j)
    change f (b a ⟨i, j.succ⟩ : E a) - (a : K) • (b a ⟨i, j.succ⟩ : E a) =
      (b a ⟨i, j.castSucc⟩ : E a) at h
    rw [sub_eq_iff_eq_add] at h
    simpa only [add_comm] using h
  let hinter : DirectSum.IsInternal E := by
    simpa only [E, S] using jordan_isInternal_maxGenEigenspace_roots f hf
  let B := hinter.collectedBasis b
  let I := Σ a : S, Fin (k a)
  let dI : I → ℕ := fun q ↦ d q.1 q.2
  let μI : I → K := fun q ↦ (q.1 : K)
  let eassoc : (Σ a : S, Σ i : Fin (k a), Fin (d a i + 1)) ≃
      (Σ q : I, Fin (dI q + 1)) :=
    (Equiv.sigmaAssoc (fun a (i : Fin (k a)) ↦ Fin (d a i + 1))).symm
  let BI := B.reindex eassoc
  have hzeroI : ∀ q, f (BI ⟨q, 0⟩) = μI q • BI ⟨q, 0⟩ := by
    rintro ⟨a, i⟩
    simpa [BI, B, eassoc, dI, μI, Basis.reindex_apply, Equiv.sigmaAssoc,
      DirectSum.IsInternal.collectedBasis_coe] using hzeroV a i
  have hsuccI : ∀ q (j : Fin (dI q)),
      f (BI ⟨q, j.succ⟩) = μI q • BI ⟨q, j.succ⟩ + BI ⟨q, j.castSucc⟩ := by
    rintro ⟨a, i⟩ j
    simpa [BI, B, eassoc, dI, μI, Basis.reindex_apply, Equiv.sigmaAssoc,
      DirectSum.IsInternal.collectedBasis_coe] using hsuccV a i j
  let eI := Fintype.equivFin I
  let d' : Fin (Fintype.card I) → ℕ := fun i ↦ dI (eI.symm i)
  let μ' : Fin (Fintype.card I) → K := fun i ↦ μI (eI.symm i)
  let eσ : (Σ q, Fin (dI q + 1)) ≃ (Σ i, Fin (d' i + 1)) :=
    Equiv.sigmaCongrLeft' eI
  let b' := BI.reindex eσ
  have hzero' : ∀ i, f (b' ⟨i, 0⟩) = μ' i • b' ⟨i, 0⟩ := by
    intro i
    simpa [b', eσ, d', μ', eI, Basis.reindex_apply, Equiv.sigmaCongrLeft'] using
      hzeroI (eI.symm i)
  have hsucc' : ∀ i (j : Fin (d' i)),
      f (b' ⟨i, j.succ⟩) = μ' i • b' ⟨i, j.succ⟩ + b' ⟨i, j.castSucc⟩ := by
    intro i j
    simpa [b', eσ, d', μ', eI, Basis.reindex_apply, Equiv.sigmaCongrLeft'] using
      hsuccI (eI.symm i) j
  refine ⟨Fintype.card I, d', μ', b', hzero', hsucc', ?_⟩
  exact LinearMap.toMatrix_eq_blockDiagonal_jordanBlock d' b' f μ' hzero' hsucc'

end Module.End

namespace MathlibExt.LinearAlgebra.Matrix.JordanNormalFormWanted

/--
**Jordan normal form.** Let $A$ be a square matrix over a field $K$, with rows and columns indexed
by a finite set $N$, whose characteristic polynomial splits into linear factors over $K$. Then $A$
is similar to a block-diagonal matrix of Jordan blocks: there are $k \in \mathbb{N}$, positive
integers $s_0, \dots, s_{k-1}$, scalars $\mu_0, \dots, \mu_{k-1} \in K$, an invertible matrix $P$
with rows and columns indexed by $N$, and a bijection $e$ from the set of pairs $(i, r)$ with
$i < k$ and $r < s_i$ onto $N$, such that $A = P J P^{-1}$, where $J$ is the block-diagonal
matrix whose $i$-th diagonal block is the Jordan block of size $s_i$ with eigenvalue $\mu_i$,
with its rows and columns relabelled by $e$.

Proof: Decompose into the maximal generalized eigenspaces (Axler, Linear Algebra Done Right,
4th ed., 8.22), take a Jordan-chain basis of each nilpotent restriction, and collect them as in
the proof of Axler 8.46. The nilpotent case is proved by induction on the range, extending chains
by preimages and adding kernel vectors, as in Wikipedia, "Jordan normal form", section "A proof".

Proves `Wanted` entry `exists_jordan_normal_form_of_splits`.

Sources: Mathlib `docs/undergrad.yaml`, Linear algebra / Structure theory of endomorphisms /
Jordan normal form; R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University
Press (2013), Theorem 3.4.1.
-/
theorem exists_jordan_normal_form_of_splits
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (h : A.charpoly.Splits) :
    ∃ (k : ℕ) (s : Fin k → ℕ) (μ : Fin k → K) (P : Matrix n n K)
      (e : (Σ i, Fin (s i)) ≃ n),
      (∀ i, 0 < s i) ∧ IsUnit P ∧
        A = P * Matrix.reindex e e
          (Matrix.blockDiagonal' (fun i => jordanBlock (s i) (μ i))) * P⁻¹ := by
  classical
  let f := Matrix.toLin' A
  let std := Pi.basisFun K n
  have hf : f.charpoly.Splits := by
    simpa only [f, Matrix.charpoly_toLin'] using h
  obtain ⟨k, d, μ, b, hzero, hsucc, hJ⟩ :=
    Module.End.exists_jordanBasis_of_charpoly_splits f hf
  let s : Fin k → ℕ := fun i ↦ d i + 1
  let e : (Σ i, Fin (s i)) ≃ n := b.indexEquiv std
  let bN := b.reindex e
  let P := std.toMatrix bN
  have hright : P * bN.toMatrix std = 1 := by
    simpa only [P] using Basis.toMatrix_mul_toMatrix_flip std bN
  have hP : IsUnit P := IsUnit.of_mul_eq_one _ hright
  have hinv : P⁻¹ = bN.toMatrix std := Matrix.inv_eq_right_inv hright
  have hJN : LinearMap.toMatrix bN bN f = Matrix.reindex e e
      (Matrix.blockDiagonal' (fun i ↦ jordanBlock (s i) (μ i))) := by
    ext i j
    simp only [LinearMap.toMatrix_apply, bN, Basis.reindex_apply,
      Basis.repr_reindex_apply, Matrix.reindex_apply]
    have hentry := congrFun (congrFun hJ (e.symm i)) (e.symm j)
    simpa only [s, LinearMap.toMatrix_apply, Matrix.submatrix_apply] using hentry
  have hchange :
      P * LinearMap.toMatrix bN bN f * bN.toMatrix std = A := by
    calc
      P * LinearMap.toMatrix bN bN f * bN.toMatrix std =
          LinearMap.toMatrix std std f := by
            simpa only [P] using
              basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix std bN std bN f
      _ = A := by
        simp only [f, std, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  refine ⟨k, s, μ, P, e, ?_, hP, ?_⟩
  · intro i
    simp only [s]
    omega
  · calc
      A = P * LinearMap.toMatrix bN bN f * bN.toMatrix std := hchange.symm
      _ = P * Matrix.reindex e e
          (Matrix.blockDiagonal' (fun i ↦ jordanBlock (s i) (μ i))) * P⁻¹ := by
        rw [hJN, hinv]

end MathlibExt.LinearAlgebra.Matrix.JordanNormalFormWanted
