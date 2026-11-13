/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.TuringBranches

/-!
# Pattern branches of the Turing system from a Lyapunov–Schmidt reduction

The steady states of the two-species Turing system `0 = d_u u_xx + f(u, v)`,
`0 = d v_xx + g(u, v)` near a homogeneous state are the zeros of a map `F(w, d)` in the
perturbation `w ∈ E` and the inhibitor diffusion `d`. This file combines

* a **Lyapunov–Schmidt reduction** of `F` at `(0, d₀)` to a scalar bifurcation function
  `g(a, d)` in the amplitude `a` of a critical mode `φ`, which enters as explicit hypotheses
  (the reduction itself is the subject of `MathlibExt.Biology.Dynamics.TuringBranchesPDE`,
  not imported here), with
* the reduced **Crandall–Rabinowitz** branch theorem for the Turing system,
  `MathlibExt.Biology.Dynamics.TuringBranches.turing_patternBranch` (imported and applied),

and concludes that `F` has a local pattern branch: a curve of nonzero steady states
`w = a φ + W(a, β(a))` at `d = β(a)` bifurcating from `(0, d₀)`, which together with the trivial
branch `w = 0` exhausts the zeros of `F` near `(0, d₀)`.

## Source receipt

* **Lyapunov–Schmidt reduction**: H. Kielhöfer, *Bifurcation Theory: An Introduction with
  Applications to Partial Differential Equations*, 2nd ed., Springer (2012), §I.2: near
  `(0, λ₀)` the solutions of `F(x, λ) = 0` are `x = v + ψ(v, λ)` with `v` in the kernel and
  `Φ(v, λ) = 0`. Taken as hypotheses, in the form of the conclusions of `lyapunovSchmidt_scalar`,
  `eventually_lsSolution_zero` and `exists_hasStrictFDerivAt_lsSolution` of the open
  `TuringBranchesPDE` (T113) together with its factorization hypothesis `hfac`: the reduction
  `hred`, the trivial branch `hW0`, continuity `hWc`, the kernel coordinate `κ` (`κ φ = 1`,
  `κ ∘ W = 0`, the projection onto `ℝ φ` along the complement containing `W`), and `hfac`.
  The hypotheses mention none of that file's definitions; `W` and `g` are arbitrary maps.
* **Bifurcation from a simple eigenvalue**: M. G. Crandall and P. H. Rabinowitz, *Bifurcation
  from simple eigenvalues*, J. Funct. Anal. 8 (1971) 321–340, Theorem 1.7. Reused, not
  reproved: `turing_patternBranch` (T55) gives transversality from the Turing data, the reduced
  branch `d = β(a)` with its slope, the local zero set of `a G(a, d)`, and the sign change of the
  critical eigenvalue.
* **Turing instability**: A. M. Turing, *The chemical basis of morphogenesis*, Phil. Trans. R.
  Soc. Lond. B 237 (1952) 37–72; J. D. Murray, *Mathematical Biology II*, 3rd ed., Springer
  (2003), ch. 2.

Proved here: the transfer of the reduced zero set to the zero set of `F`, and the fact that the
branch states are nonzero.

## Main result

* `turing_patternBranch_of_reduction`: under the reduction hypotheses and the Turing data of an
  admissible mode `k` at its neutral diffusion `d₀`, the crossing is transversal, the zeros of
  `F` near `(0, d₀)` are exactly the trivial branch and the pattern branch, the branch states
  are nonzero steady states, and the critical eigenvalue changes sign at `d₀`.

## Scope

No nonlinear Turing map `F` is constructed and the reduction is not proved here. As in
`turing_patternBranch`, only the selected mode `k` is controlled: the hypotheses say nothing
about the other Neumann modes, so nothing is claimed about the stability of the homogeneous
state or of the branch in the full problem.
-/

@[expose] public section

open Filter Topology

namespace MathlibExt.Biology.Dynamics.TuringBranchApplication

open MathlibExt.Biology.Dynamics.TuringPatterns MathlibExt.Biology.Dynamics.TuringBranches

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Zero Y]

/-- **Turing pattern branch of the full problem.** Let `F : E × ℝ → Y` be the steady-state map of
the Turing system in the perturbation `w` and the inhibitor diffusion `d`, and suppose it has a
Lyapunov–Schmidt reduction at `(0, d₀)` along a critical mode `φ`: there are a continuous linear
kernel coordinate `κ` with `κ φ = 1`, a correction `W : ℝ × ℝ → E` with values in `ker κ`,
continuous at `(0, d₀)` and vanishing on the trivial branch, and a scalar bifurcation function
`g` such that near `(0, d₀)`

* `F(w, d) = 0 ↔ ∃ a, w = a φ + W(a, d) ∧ g(a, d) = 0` (`hred`), and
* `g(a, d) = a G(a, d)` (`hfac`).

Let mode `k` be admissible (`0 < f_u k² - d_u k⁴`) with neutral diffusion `d₀ = d_n(k²)` and
negative trace there, and let `G` be strictly differentiable at `(0, d₀)` and equal on the
trivial branch to the critical eigenvalue `leadingEigenvalue (J - k² D(d))`. Then

* the crossing is transversal, `0 < ∂_d G(0, d₀)`;
* there is a branch `d = β(a)` with `β 0 = d₀` and slope `-∂_a G / ∂_d G` at `0` such that near
  `(0, d₀)` the zeros of `F` are exactly the trivial ones `w = 0` and the branch
  `w = a φ + W(a, d)`, `d = β(a)`;
* for small `a ≠ 0` the branch state `a φ + W(a, β(a))` is a **nonzero** steady state at
  `d = β(a)` (a pattern);
* the critical eigenvalue `G(0, d)` of mode `k` is negative for `d < d₀` and positive for
  `d > d₀` near `d₀`. -/
theorem turing_patternBranch_of_reduction {F : E × ℝ → Y} {φ : E} {κ : E →L[ℝ] ℝ}
    {W : ℝ × ℝ → E} {g : ℝ × ℝ → ℝ} {J : Matrix (Fin 2) (Fin 2) ℝ} {du k d₀ : ℝ}
    {G : ℝ × ℝ → ℝ} {G' : ℝ × ℝ →L[ℝ] ℝ}
    (hκφ : κ φ = 1) (hκW : ∀ p, κ (W p) = 0)
    (hW0 : ∀ᶠ d in 𝓝 d₀, W (0, d) = 0) (hWc : ContinuousAt W (0, d₀))
    (hred : ∀ᶠ q in 𝓝 ((0 : E), d₀), F q = 0 ↔ ∃ a : ℝ, q.1 = a • φ + W (a, q.2) ∧ g (a, q.2) = 0)
    (hfac : ∀ᶠ p in 𝓝 ((0 : ℝ), d₀), g p = p.1 * G p)
    (htr : J.trace - k ^ 2 * (du + d₀) < 0) (hk : 0 < J 0 0 * k ^ 2 - du * (k ^ 2) ^ 2)
    (hd₀ : d₀ = neutralDiffusion J du (k ^ 2)) (hG : HasStrictFDerivAt G G' (0, d₀))
    (hlin : ∀ᶠ d in 𝓝 d₀, G (0, d) = leadingEigenvalue (modeMatrix J du d k)) :
    0 < G' (0, 1) ∧
      ∃ β : ℝ → ℝ, β 0 = d₀ ∧ HasStrictDerivAt β (-(G' (1, 0) / G' (0, 1))) 0 ∧
        (∀ᶠ q in 𝓝 ((0 : E), d₀), (F q = 0 ↔ q.1 = 0 ∨
          ∃ a : ℝ, q.1 = a • φ + W (a, q.2) ∧ q.2 = β a)) ∧
        (∀ᶠ a in 𝓝[≠] (0 : ℝ), F (a • φ + W (a, β a), β a) = 0 ∧ a • φ + W (a, β a) ≠ 0) ∧
        (∀ᶠ d in 𝓝[<] d₀, G (0, d) < 0) ∧ ∀ᶠ d in 𝓝[>] d₀, 0 < G (0, d) := by
  obtain ⟨hσ, ⟨β, hβ0, hβd, hβz⟩, hleft, hright⟩ := turing_patternBranch htr hk hd₀ hG hlin
  -- The kernel coordinate of `a φ + W(a, d)` is `a`.
  have hcoord : ∀ (a : ℝ) (d : ℝ), κ (a • φ + W (a, d)) = a := fun a d => by
    rw [map_add, map_smul, hκφ, hκW, smul_eq_mul, mul_one, add_zero]
  have hsnd : Tendsto (fun q : E × ℝ => q.2) (𝓝 ((0 : E), d₀)) (𝓝 d₀) :=
    continuous_snd.tendsto _
  have ht : Tendsto (fun q : E × ℝ => (κ q.1, q.2)) (𝓝 ((0 : E), d₀)) (𝓝 ((0 : ℝ), d₀)) := by
    have h := ((κ.continuous.comp continuous_fst).prodMk continuous_snd).tendsto ((0 : E), d₀)
    simpa using h
  have hmain : ∀ᶠ q in 𝓝 ((0 : E), d₀), (F q = 0 ↔ q.1 = 0 ∨
      ∃ a : ℝ, q.1 = a • φ + W (a, q.2) ∧ q.2 = β a) := by
    filter_upwards [hred, ht.eventually hfac, ht.eventually hβz, hsnd.eventually hW0]
      with q hq hfacq hβq hWq
    rw [hq]
    constructor
    · rintro ⟨a, hx, hga⟩
      have ha : κ q.1 = a := by rw [hx, hcoord]
      rw [ha] at hfacq hβq
      rcases (hβq.1 (hfacq ▸ hga)) with ha0 | hd
      · left
        rw [hx, ha0, zero_smul, zero_add, hWq]
      · exact Or.inr ⟨a, hx, hd⟩
    · rintro (h0 | ⟨a, hx, hd⟩)
      · refine ⟨0, by rw [h0, zero_smul, zero_add, hWq], ?_⟩
        rw [h0, map_zero] at hfacq
        rw [hfacq, zero_mul]
      · have ha : κ q.1 = a := by rw [hx, hcoord]
        rw [ha] at hfacq hβq
        exact ⟨a, hx, hfacq.trans (hβq.2 (Or.inr hd))⟩
  refine ⟨hσ, β, hβ0, hβd, hmain, ?_, hleft, hright⟩
  have hβc : Tendsto β (𝓝 0) (𝓝 d₀) := hβ0 ▸ hβd.hasDerivAt.continuousAt.tendsto
  have hWt : Tendsto (fun a : ℝ => W (a, β a)) (𝓝 0) (𝓝 0) := by
    have h := hWc.tendsto.comp (tendsto_id.prodMk_nhds hβc)
    rwa [hW0.self_of_nhds] at h
  have hA : Tendsto (fun a : ℝ => a • φ) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).smul_const φ
  have h2 : Tendsto (fun a : ℝ => (a • φ + W (a, β a), β a)) (𝓝 0) (𝓝 ((0 : E), d₀)) := by
    simpa using (hA.add hWt).prodMk_nhds hβc
  filter_upwards [nhdsWithin_le_nhds (h2.eventually hmain), self_mem_nhdsWithin] with a ha ha0
  refine ⟨ha.2 (Or.inr ⟨a, rfl, rfl⟩), fun h => ha0 ?_⟩
  rw [← hcoord a (β a), h, map_zero]
  exact Set.mem_singleton 0

end MathlibExt.Biology.Dynamics.TuringBranchApplication
