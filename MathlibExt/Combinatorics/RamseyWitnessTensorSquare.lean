/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Compactification.StoneCech

/-!
# Ramsey's witnesses and tensor squares of ultrafilters

An ultrafilter `W` on `ℕ × ℕ` is a *Ramsey's witness* when every member of `W` contains
`[H]² = {(h, h') ∈ H × H | h < h'}` for some infinite `H ⊆ ℕ`. The tensor square of an ultrafilter
`U` on `ℕ` is `U ⊗ U = U.bind fun n => U.map (Prod.mk n)`, so that `X ∈ U ⊗ U` if and only if
`{n | {m | (n, m) ∈ X} ∈ U} ∈ U`. The theorem below, from the paper of Di Nasso and Jin cited in
its docstring, says that the Ramsey's witnesses are exactly the points of the closure, in the
Stone–Čech topology of `Ultrafilter (ℕ × ℕ)`, of the tensor squares of the non-principal
ultrafilters on `ℕ`.

## Main statements

* `MetaMathlibExt.ramseyWitness_iff_mem_closure_tensor_squares`: an ultrafilter on `ℕ × ℕ` is a
  Ramsey's witness if and only if it lies in the closure of the tensor squares `U ⊗ U` of the
  non-principal ultrafilters `U` on `ℕ`.

## Proof

The basic open sets `{u | s ∈ u}` form a basis of the topology on ultrafilters, so `W` lies in the
closure of a set `𝒮` of ultrafilters exactly when every member of `W` belongs to some element of
`𝒮`. If `X ∈ U ⊗ U` for a non-principal `U`, we choose `h₀ < h₁ < h₂ < ⋯` greedily: each `hₖ` lies
in the `U`-large set of the `n` with `{m | (n, m) ∈ X} ∈ U` and in the sections of `X` at
`h₀, …, hₖ₋₁`, all of which belong to `U`. The range of this sequence is an infinite set `H` with
`[H]² ⊆ X`. Conversely, if `[H]² ⊆ X` for an infinite `H`, then `X ∈ U ⊗ U` for every
non-principal ultrafilter `U` containing `H`, since the section of `X` at each `h ∈ H` contains
the cofinite part `{h' ∈ H | h < h'}` of `H`.
-/

open Filter

namespace MetaMathlibExt

namespace ramseyWitness_iff_mem_closure_tensor_squares

/-- A non-principal ultrafilter on `ℕ` contains every final segment `(x, ∞)`. -/
private theorem Ioi_mem {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite) (x : ℕ) :
    Set.Ioi x ∈ U :=
  hU (Nat.cofinite_eq_atTop ▸ Ioi_mem_atTop x)

/-- If `X` lies in the tensor square `U ⊗ U` of a non-principal ultrafilter `U` on `ℕ`, then `X`
contains the pairs `(h i, h j)`, `i < j`, of some strictly increasing sequence `h`. -/
private theorem exists_strictMono_of_mem_tensor {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite) {X : Set (ℕ × ℕ)}
    (hX : {n | {m | (n, m) ∈ X} ∈ U} ∈ U) :
    ∃ h : ℕ → ℕ, StrictMono h ∧ ∀ i j, i < j → (h i, h j) ∈ X := by
  set A := {n | {m | (n, m) ∈ X} ∈ U}
  -- From a large set `S ⊆ A`, pick a point `x` and keep the large set of the later points of `S`
  -- in the section of `X` at `x`.
  have key : ∀ S : Set ℕ, S ∈ U → S ⊆ A →
      ∃ x ∈ S, S ∩ {m | (x, m) ∈ X} ∩ Set.Ioi x ∈ U := fun S hS hSA =>
    let ⟨x, hx⟩ := U.nonempty_of_mem hS
    ⟨x, hx, inter_mem (inter_mem hS (hSA hx)) (Ioi_mem hU x)⟩
  choose! pick hpick_mem hpick using key
  let next : Set ℕ → Set ℕ := fun S => S ∩ {m | (pick S, m) ∈ X} ∩ Set.Ioi (pick S)
  let S : ℕ → Set ℕ := fun k => next^[k] A
  have hS_succ (k : ℕ) : S (k + 1) = next (S k) := Function.iterate_succ_apply' next k A
  have hS (k : ℕ) : S k ∈ U ∧ S k ⊆ A := by
    induction k with
    | zero => exact ⟨hX, subset_rfl⟩
    | succ k ih =>
      rw [hS_succ]
      exact ⟨hpick _ ih.1 ih.2, Set.inter_subset_left.trans (Set.inter_subset_left.trans ih.2)⟩
  have hS_anti : Antitone S := antitone_nat_of_succ_le fun k => by
    rw [hS_succ]
    exact Set.inter_subset_left.trans Set.inter_subset_left
  have hstep (i j : ℕ) (hij : i < j) :
      (pick (S i), pick (S j)) ∈ X ∧ pick (S i) < pick (S j) := by
    have hmem : pick (S j) ∈ next (S i) :=
      hS_succ i ▸ hS_anti (Nat.succ_le_of_lt hij) (hpick_mem _ (hS j).1 (hS j).2)
    exact ⟨hmem.1.2, hmem.2⟩
  exact ⟨fun k => pick (S k), strictMono_nat_of_lt_succ fun k => (hstep k (k + 1) k.lt_succ_self).2,
    fun i j hij => (hstep i j hij).1⟩

end ramseyWitness_iff_mem_closure_tensor_squares

open ramseyWitness_iff_mem_closure_tensor_squares in
/-- **Ramsey's witnesses are the closure of tensor squares.** For an ultrafilter $U$ on
$\mathbb{N} = \{0, 1, 2, \dots\}$, the tensor square $U \otimes U$ is the ultrafilter on
$\mathbb{N} \times \mathbb{N}$ whose members are the sets $X$ with
$\{n : \{m : (n, m) \in X\} \in U\} \in U$. An ultrafilter $W$ on $\mathbb{N} \times \mathbb{N}$ is
a Ramsey's witness when every $X \in W$ contains $[H]^2 = \{(h, h') \in H \times H : h < h'\}$ for
some infinite $H \subseteq \mathbb{N}$. An ultrafilter $W$ on $\mathbb{N} \times \mathbb{N}$ is a
Ramsey's witness if and only if $W$ lies in the closure, in the Stone–Čech space
$\beta(\mathbb{N} \times \mathbb{N})$, of the set of tensor squares $U \otimes U$ of non-principal
ultrafilters $U$ on $\mathbb{N}$.

Source: Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum Theorem*,
INTEGERS 25 (2025), Article A105, Proposition 3.5 (`integers-2025-A105-prop-3-5`). -/
public theorem ramseyWitness_iff_mem_closure_tensor_squares (W : Ultrafilter (ℕ × ℕ)) :
    (∀ X ∈ W, ∃ H : Set ℕ, H.Infinite ∧ ∀ h ∈ H, ∀ h' ∈ H, h < h' → (h, h') ∈ X) ↔
      W ∈ closure {V : Ultrafilter (ℕ × ℕ) | ∃ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ cofinite ∧
        V = U.bind fun n => U.map (Prod.mk n)} := by
  rw [ultrafilterBasis_is_basis.mem_closure_iff]
  constructor
  · -- A Ramsey's witness: each `X ∈ W` lies in `U ⊗ U` for a non-principal `U` containing the
    -- infinite set `H` given by `X`.
    rintro hW _ ⟨X, rfl⟩ hXW
    obtain ⟨H, hH, hHX⟩ := hW X hXW
    have := cofinite_inf_principal_neBot_iff.2 hH
    set U := Ultrafilter.of (cofinite ⊓ 𝓟 H)
    have hU : (U : Filter ℕ) ≤ cofinite ⊓ 𝓟 H := Ultrafilter.of_le _
    have hUcof : (U : Filter ℕ) ≤ cofinite := hU.trans inf_le_left
    have hHU : H ∈ U := hU (mem_inf_of_right (mem_principal_self H))
    refine ⟨U.bind fun n => U.map (Prod.mk n), ?_, U, hUcof, rfl⟩
    change {n | {m | (n, m) ∈ X} ∈ U} ∈ U
    exact mem_of_superset hHU fun n hn =>
      mem_of_superset (inter_mem hHU (Ioi_mem hUcof n)) fun m hm => hHX n hn m hm.1 hm.2
  · -- A point of the closure: each `X ∈ W` lies in some `U ⊗ U`, hence contains some `[H]²`.
    intro hW X hXW
    obtain ⟨V, hXV, U, hU, rfl⟩ := hW _ ⟨X, rfl⟩ hXW
    obtain ⟨h, hh, hhX⟩ := exists_strictMono_of_mem_tensor hU hXV
    refine ⟨Set.range h, Set.infinite_range_of_injective hh.injective, ?_⟩
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    exact hhX i j (hh.lt_iff_lt.1 hij)

end MetaMathlibExt
