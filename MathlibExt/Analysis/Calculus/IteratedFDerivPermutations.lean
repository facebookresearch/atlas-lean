/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.Calculus.IteratedFDerivSymmetric
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Permutation symmetry of iterated Fréchet derivatives

Let E and F be normed real vector spaces, n ∈ ℕ, and f : E → F be C^n.
At each x, D^n f(x) is invariant under every permutation of its n directions.
The case n = 0 and repeated directions are included. A C∞ map has this
symmetry at every finite order.

This symmetry is used for unordered elementary differentials in
Ketcheson–Ranocha, *Computing with B-series*, arXiv:2111.11680v2, equations 11–12.
-/

@[expose] public section

open scoped ContDiff

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- For normed real vector spaces E,F and a continuous n-multilinear map L : E^n → F,
the permutations of Fin n preserving every evaluation of L form a submonoid. -/
private def invariantSubmonoid {n : ℕ} (L : E [×n]→L[ℝ] F) :
    Submonoid (Equiv.Perm (Fin n)) where
  carrier := {σ | ∀ m : Fin n → E, L (m ∘ σ) = L m}
  one_mem' := by intro m; simp
  mul_mem' := by
    intro σ τ hσ hτ m
    calc
      L (m ∘ (σ * τ : Equiv.Perm (Fin n))) = L ((m ∘ σ) ∘ τ) := rfl
      _ = L (m ∘ σ) := hτ (m ∘ σ)
      _ = L m := hσ m

/-- Let E and F be normed real vector spaces and N ∈ ℕ. Every C^N map f : E → F
satisfies D^N f(x)(m ∘ σ) = D^N f(x)(m) for all x : E, m : Fin N → E
and permutations σ of Fin N. -/
private theorem iteratedFDeriv_comp_perm_nat (N : ℕ) :
    ∀ (f : E → F), ContDiff ℝ (N : ℕ) f →
      ∀ (x : E) (m : Fin N → E) (σ : Equiv.Perm (Fin N)),
        iteratedFDeriv ℝ N f x (m ∘ σ) = iteratedFDeriv ℝ N f x m := by
  induction N with
  | zero => intro f hf x m σ; simp
  | succ N ih =>
      intro f hf x m σ
      have hbelow : (N : ℕ∞ω) < (N + 1 : ℕ) := by norm_cast; omega
      have hD : Differentiable ℝ (iteratedFDeriv ℝ N f) :=
        ContDiff.differentiable_iteratedFDeriv hbelow hf
      have hlow : ContDiff ℝ (N : ℕ) f := hf.of_le hbelow.le
      let S := invariantSubmonoid (iteratedFDeriv ℝ (N + 1) f x)
      have hgenerators : Set.range (fun i : Fin N ↦ Equiv.swap i.castSucc i.succ) ⊆ S := by
        rintro τ ⟨i, rfl⟩
        change ∀ v : Fin (N + 1) → E,
          iteratedFDeriv ℝ (N + 1) f x (v ∘ Equiv.swap i.castSucc i.succ) =
            iteratedFDeriv ℝ (N + 1) f x v
        intro v
        cases N with
        | zero => exact Fin.elim0 i
        | succ n =>
            cases i using Fin.cases with
            | zero => simpa using hf.iteratedFDeriv_comp_swap_zero_one x v
            | succ j =>
                let τ : Equiv.Perm (Fin (n + 1)) := Equiv.swap j.castSucc j.succ
                have heq : (fun y ↦ iteratedFDeriv ℝ (n + 1) f y (Fin.tail v ∘ τ)) =
                    (fun y ↦ iteratedFDeriv ℝ (n + 1) f y (Fin.tail v)) := by
                  funext y
                  exact ih f hlow y (Fin.tail v) τ
                have hv : v ∘ Equiv.swap j.succ.castSucc j.succ.succ =
                    Fin.cons (v 0) (Fin.tail v ∘ τ) := by
                  simpa only [Matrix.vecCons, Fin.cons_self_tail, Fin.castSucc_succ, τ] using
                    (Matrix.cons_swap (v 0) (Fin.tail v) j.castSucc j.succ).symm
                rw [hv]
                calc
                  iteratedFDeriv ℝ (n + 2) f x (Fin.cons (v 0) (Fin.tail v ∘ τ)) =
                      fderiv ℝ (fun y ↦ iteratedFDeriv ℝ (n + 1) f y (Fin.tail v ∘ τ)) x (v 0) := by
                    simpa only [Fin.tail_cons, Fin.cons_zero] using
                      (hD x).iteratedFDeriv_succ_apply_left'
                        (m := Fin.cons (v 0) (Fin.tail v ∘ τ))
                  _ = fderiv ℝ (fun y ↦ iteratedFDeriv ℝ (n + 1) f y (Fin.tail v)) x (v 0) := by
                    rw [heq]
                  _ = iteratedFDeriv ℝ (n + 2) f x v :=
                    ((hD x).iteratedFDeriv_succ_apply_left' (m := v)).symm
      have hclosure : Submonoid.closure
          (Set.range fun i : Fin N ↦ Equiv.swap i.castSucc i.succ) ≤ S :=
        Submonoid.closure_le.mpr hgenerators
      have hσ : σ ∈ S := hclosure (by rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial)
      exact hσ m

/-- Let E and F be normed real vector spaces, n ∈ ℕ, and f : E → F be C^n.
For x : E, m : Fin n → E and any permutation σ of Fin n,
D^n f(x)(m ∘ σ) = D^n f(x)(m), including the empty family n = 0. -/
theorem ContDiff.iteratedFDeriv_comp_perm {f : E → F} {n : ℕ}
    (hf : ContDiff ℝ (n : ℕ) f) (x : E) (m : Fin n → E) (σ : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℝ n f x (m ∘ σ) = iteratedFDeriv ℝ n f x m :=
  iteratedFDeriv_comp_perm_nat n f hf x m σ

/-- Let E and F be normed real vector spaces, n ∈ ℕ, and f : E → F be C^n.
At each x : E, the continuous n-multilinear map D^n f(x) is unchanged
by reindexing its inputs with any permutation of Fin n. -/
theorem ContDiff.domDomCongr_iteratedFDeriv {f : E → F} {n : ℕ}
    (hf : ContDiff ℝ (n : ℕ) f) (x : E) (σ : Equiv.Perm (Fin n)) :
    (iteratedFDeriv ℝ n f x).domDomCongr σ = iteratedFDeriv ℝ n f x := by
  ext m
  exact hf.iteratedFDeriv_comp_perm x m σ

/-- Let E and F be normed real vector spaces and f : E → F be C∞.
For every n ∈ ℕ, x : E, m : Fin n → E and permutation σ of Fin n,
D^n f(x)(m ∘ σ) = D^n f(x)(m). -/
theorem ContDiff.iteratedFDeriv_comp_perm_of_infty {f : E → F} {n : ℕ}
    (hf : ContDiff ℝ ∞ f) (x : E) (m : Fin n → E) (σ : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℝ n f x (m ∘ σ) = iteratedFDeriv ℝ n f x m :=
  (hf.of_le (by simp) : ContDiff ℝ (n : ℕ) f).iteratedFDeriv_comp_perm x m σ

/-- Let E and F be normed real vector spaces and f : E → F be C∞.
For every n ∈ ℕ and x : E, the continuous n-multilinear map D^n f(x)
is invariant under every permutation of Fin n. -/
theorem ContDiff.domDomCongr_iteratedFDeriv_of_infty {f : E → F} {n : ℕ}
    (hf : ContDiff ℝ ∞ f) (x : E) (σ : Equiv.Perm (Fin n)) :
    (iteratedFDeriv ℝ n f x).domDomCongr σ = iteratedFDeriv ℝ n f x :=
  (hf.of_le (by simp) : ContDiff ℝ (n : ℕ) f).domDomCongr_iteratedFDeriv x σ
