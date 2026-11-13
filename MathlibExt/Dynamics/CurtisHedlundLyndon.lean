/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Constructions
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Topology.NoetherianSpace

@[expose] public section

namespace MetaMathlibExt

private theorem perpoint {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [DiscreteTopology B]
  (G : (ℤ → A) → B) (hG : Continuous G) (x : ℤ → A) :
  ∃ I : Finset ℤ, ∀ y : ℤ → A, (∀ i ∈ I, y i = x i) → G y = G x := by
  have hmem : G ⁻¹' {G x} ∈ nhds x := by
    apply hG.continuousAt.preimage_mem_nhds
    exact (isOpen_discrete _).mem_nhds rfl
  rw [nhds_pi] at hmem
  rw [Filter.mem_pi] at hmem
  obtain ⟨I, hIfin, t, ht, hsub⟩ := hmem
  refine ⟨hIfin.toFinset, fun y hy => ?_⟩
  have hy_mem : y ∈ I.pi t := by
    rw [Set.mem_pi]
    intro i hi
    have hxi : x i ∈ t i := mem_of_mem_nhds (ht i)
    rw [hy i (hIfin.mem_toFinset.mpr hi)] at *
    exact hxi
  have := hsub hy_mem
  simpa using this

private theorem globaldep {A B : Type*} [TopologicalSpace A] [DiscreteTopology A]
  [Finite A] [TopologicalSpace B] [DiscreteTopology B]
  (G : (ℤ → A) → B) (hG : Continuous G) :
  ∃ S : Finset ℤ, ∀ x y : ℤ → A, (∀ i ∈ S, x i = y i) → G x = G y := by
  choose I hI using fun x => perpoint G hG x
  let U : (ℤ → A) → Set (ℤ → A) := fun x => {y | ∀ i ∈ I x, y i = x i}
  have hopen : ∀ x, IsOpen (U x) := by
    intro x
    have : U x = (↑(I x) : Set ℤ).pi (fun i => ({x i} : Set A)) := by
      ext y
      simp [U, Set.mem_pi]
    rw [this]
    exact isOpen_set_pi (Finset.finite_toSet _) (fun a _ => isOpen_discrete _)
  have hcover : Set.univ ⊆ ⋃ x, U x := by
    intro y _
    simp only [Set.mem_iUnion]
    exact ⟨y, fun i _ => rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hopen hcover
  refine ⟨t.biUnion I, fun x y hxy => ?_⟩
  have hxmem : x ∈ ⋃ z ∈ t, U z := ht (Set.mem_univ x)
  simp only [Set.mem_iUnion] at hxmem
  obtain ⟨z, hz, hxz⟩ := hxmem
  have hyz : y ∈ U z := by
    intro i hi
    have hiS : i ∈ t.biUnion I := Finset.mem_biUnion.mpr ⟨z, hz, hi⟩
    have h1 : x i = z i := hxz i hi
    have h2 : x i = y i := hxy i hiS
    rw [← h1, h2]
  have e1 := hI z x hxz
  have e2 := hI z y hyz
  rw [e1, e2]

private theorem aux_radius (S : Finset ℤ) : ∃ r : ℕ, ∀ i ∈ S, -(r : ℤ) ≤ i ∧ i ≤ (r : ℤ) := by
  refine ⟨(S.image (fun x => x.natAbs)).sup id, fun i hi => ?_⟩
  have hmem : i.natAbs ∈ S.image (fun x => x.natAbs) := Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hle : id i.natAbs ≤ (S.image (fun x => x.natAbs)).sup id := Finset.le_sup hmem
  simp only [id] at hle
  have hcast : ((i.natAbs : ℕ) : ℤ) ≤ (((S.image (fun x => x.natAbs)).sup id : ℕ) : ℤ) := by
    exact_mod_cast hle
  rw [Int.natCast_natAbs] at hcast
  constructor <;> linarith [abs_le.mp hcast]


/-- **Curtis–Hedlund–Lyndon theorem with an arbitrary discrete output alphabet.** Let $A$ be a
finite set and $B$ any set, both with the discrete topology, and give $A^{\mathbb{Z}}$ and
$B^{\mathbb{Z}}$ the product topology. For $k \in \mathbb{Z}$ let $\sigma^k$ be the shift on
either space given by $(\sigma^k x)_n = x_{n+k}$ for all $n \in \mathbb{Z}$. A map
$F : A^{\mathbb{Z}} \to B^{\mathbb{Z}}$ is a sliding block code, that is, there are a radius
$r \in \mathbb{N}$ and a local rule $\varphi : A^{2r+1} \to B$ with
$F(x)_n = \varphi(x_{n-r}, \dots, x_{n+r})$ for all $x \in A^{\mathbb{Z}}$ and $n \in \mathbb{Z}$,
if and only if $F$ is continuous and commutes with every shift: $F(\sigma^k x) = \sigma^k F(x)$
for all $x \in A^{\mathbb{Z}}$ and $k \in \mathbb{Z}$. -/
theorem curtis_hedlund_lyndon_general {A B : Type*} [TopologicalSpace A] [DiscreteTopology A]
    [Finite A] [TopologicalSpace B] [DiscreteTopology B] (F : (ℤ → A) → (ℤ → B)) :
    (∃ (r : ℕ) (φ : (Fin (2 * r + 1) → A) → B), ∀ (x : ℤ → A) (n : ℤ),
      F x n = φ (fun i => x (n + ((i.val : ℤ) - (r : ℤ))))) ↔
    (Continuous F ∧ ∀ (x : ℤ → A) (k : ℤ), F (fun n => x (n + k)) = fun n => F x (n + k)) := by
  constructor
  · rintro ⟨r, φ, h⟩
    constructor
    · rw [continuous_pi_iff]
      intro n
      have hfn : (fun x : ℤ → A => F x n) =
          φ ∘ (fun x : ℤ → A => (fun i : Fin (2 * r + 1) => x (n + ((i.val : ℤ) - (r : ℤ))))) := by
        funext x
        exact h x n
      rw [hfn]
      apply Continuous.comp continuous_of_discreteTopology
      rw [continuous_pi_iff]
      intro i
      exact continuous_apply _
    · intro x k
      funext n
      rw [h _ n, h _ (n + k)]
      congr 1
      funext i
      congr 1
      ring
  · rintro ⟨hcont, hcomm⟩
    have hG : Continuous (fun x : ℤ → A => F x 0) :=
      (continuous_apply 0).comp hcont
    obtain ⟨S, hS⟩ := globaldep (fun x : ℤ → A => F x 0) hG
    obtain ⟨r, hr⟩ := aux_radius S
    set E : (Fin (2 * r + 1) → A) → (ℤ → A) := fun p n =>
      if h : -(r : ℤ) ≤ n ∧ n ≤ (r : ℤ) then
        p ⟨(n + (r : ℤ)).toNat,
          (Int.toNat_lt (by linarith [h.1])).mpr (by push_cast; linarith [h.2])⟩
      else p ⟨0, by omega⟩ with hE
    refine ⟨r, fun p => (fun x : ℤ → A => F x 0) (E p), fun x n => ?_⟩
    have hFn : F x n = (fun x : ℤ → A => F x 0) (fun m => x (m + n)) := by
      have h0 : F (fun m => x (m + n)) 0 = F x (0 + n) := by
        have h1 := congrFun (hcomm x n) 0
        simpa using h1
      simpa using h0.symm
    have hagree : ∀ i ∈ S,
        E (fun j : Fin (2 * r + 1) => (fun m => x (m + n)) (((j.val : ℕ) : ℤ) - (r : ℤ))) i
          = (fun m => x (m + n)) i := by
      intro i hi
      have hri := hr i hi
      simp only [hE, dite_eq_left hri]
      congr 1
      have h0 : (0 : ℤ) ≤ i + (r : ℤ) := by linarith [hri.1]
      have hval : ((((i + (r : ℤ)).toNat : ℕ) : ℤ)) = i + (r : ℤ) := Int.toNat_of_nonneg h0
      linarith [hval]
    have key : (fun x : ℤ → A => F x 0) (fun m => x (m + n)) =
        (fun x : ℤ → A => F x 0)
          (E (fun j : Fin (2 * r + 1) => (fun m => x (m + n)) (((j.val : ℕ) : ℤ) - (r : ℤ)))) := by
      exact hS _ _ (fun i hi => (hagree i hi).symm)
    have hwin : (fun j : Fin (2 * r + 1) => (fun m => x (m + n)) (((j.val : ℕ) : ℤ) - (r : ℤ))) =
        (fun i => x (n + (((i.val : ℕ) : ℤ) - (r : ℤ)))) := by
      funext i
      change x (((((i.val : ℕ) : ℤ)) - (r : ℤ)) + n) = x (n + ((((i.val : ℕ) : ℤ)) - (r : ℤ)))
      congr 1
      ring
    rw [hFn, key, hwin]

/-- **Curtis–Hedlund–Lyndon theorem.** Let $A$ and $B$ be finite sets with the discrete
topology, and give $A^{\mathbb{Z}}$ and $B^{\mathbb{Z}}$ the product topology. For
$k \in \mathbb{Z}$ let $\sigma^k$ be the shift on either space given by
$(\sigma^k x)_n = x_{n+k}$ for all $n \in \mathbb{Z}$. A map
$F : A^{\mathbb{Z}} \to B^{\mathbb{Z}}$ is a sliding block code, that is, there are a radius
$r \in \mathbb{N}$ and a local rule $\varphi : A^{2r+1} \to B$ with
$F(x)_n = \varphi(x_{n-r}, \dots, x_{n+r})$ for all $x \in A^{\mathbb{Z}}$ and $n \in \mathbb{Z}$,
if and only if $F$ is continuous and commutes with every shift: $F(\sigma^k x) = \sigma^k F(x)$
for all $x \in A^{\mathbb{Z}}$ and $k \in \mathbb{Z}$.

Source: https://en.wikipedia.org/wiki/Curtis%E2%80%93Hedlund%E2%80%93Lyndon_theorem (statement
id `curtis-hedlund-s1`). Proves `Wanted` entry `curtis_hedlund_lyndon`.
-/
@[nolint unusedArguments]
theorem curtis_hedlund_lyndon {A B : Type*} [TopologicalSpace A] [DiscreteTopology A]
  [Finite A] [TopologicalSpace B] [DiscreteTopology B] [Finite B] (F : (ℤ → A) → (ℤ → B)) :
  (∃ (r : ℕ) (φ : (Fin (2 * r + 1) → A) → B), ∀ (x : ℤ → A) (n : ℤ), F x n = φ
  (fun i => x (n + ((i.val : ℤ) - (r : ℤ))))) ↔
  (Continuous F ∧ ∀ (x : ℤ → A) (k : ℤ), F (fun n => x (n + k)) = fun n => F x (n + k)) := by
  exact curtis_hedlund_lyndon_general F

end MetaMathlibExt
