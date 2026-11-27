/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ODE.ExplicitEuler

/-!
# Residual networks as discretised flows

A residual network of depth `L` with the `1/L` scaling updates its hidden state by
`z_{l+1} = z_l + (1/L) g_l(z_l)`, `l = 0, …, L - 1`: it is the explicit Euler scheme with step
`1/L` for an ordinary differential equation `ż = g(t, z)` on `[0, 1]`. This is the dynamical-systems
view of deep learning of W. E (*A proposal on machine learning via dynamical systems*,
Commun. Math. Stat. 5 (2017)) and of W. E, J. Han and Q. Li (*A mean-field optimal control
formulation of deep learning*, Res. Math. Sci. 6 (2019), §3, equation (1)); W. E, C. Ma,
S. Wojtowytsch and L. Wu (*Towards a mathematical understanding of neural network-based machine
learning: what we know and what we don't*, CSIAM Trans. Appl. Math. (2020), §3.3) write the
scaled residual network `z_{l+1} = z_l + (1/L) U_l σ(W_l z_l)` and its continuous-depth limit.

When the block of layer `l` is `g(l/L, ·)` for a time-dependent vector field `g` that is `C²`
jointly and Lipschitz in the state, `residualNetwork_flow_error_le` shows that the output of the
depth-`L` network is within `C / L` of the time-`1` value of the flow, uniformly in the depth. It
is the first-order convergence of the explicit Euler method,
`MathlibExt.Analysis.ODE.ExplicitEulerWanted.explicit_euler_first_order_convergence`, at
`t₀ = 0`, `T = 1` and step `h = 1/L`. The `C²` hypothesis excludes ReLU blocks. The blocks
`U(t) σ(W(t) z)` are covered when the weights depend smoothly on the depth variable and `σ` is
`C²` with bounded derivative (e.g. `tanh`), so that the block is globally Lipschitz in the state;
a `C²` activation alone is not enough (`σ(s) = s²` gives `ż = z²`, which blows up).
-/

@[expose] public section

set_option autoImplicit false

namespace CSLibExt.MachineLearning.NeuralNetworks

/-- **Residual networks converge to their continuous-depth flow at rate `1/L`.** Let `g : ℝ → E → E`
be `C²` as a function of `(t, z)` and `K`-Lipschitz in `z` for every `t ∈ [0, 1]`, and let
`z₀ ∈ E`. Then the flow `ż = g(t, z)`, `z(0) = z₀`, exists on `[0, 1]`, and there is a constant
`C` such that for every depth `L ≥ 1`, the residual network
`Z_0 = z₀`, `Z_{l+1} = Z_l + (1/L) g(l/L, Z_l)` satisfies `‖Z_L - z(1)‖ ≤ C / L`.
This is the residual network as the forward Euler discretisation of an ODE (W. E, J. Han and
Q. Li, *A mean-field optimal control formulation of deep learning*, Res. Math. Sci. 6 (2019), §3,
equation (1) and its continuous-time idealisation; W. E, C. Ma, S. Wojtowytsch and L. Wu,
*Towards a mathematical understanding of neural network-based machine learning*, §3.3), and the
bound is the first-order convergence of the explicit Euler method
(`explicit_euler_first_order_convergence`) with step `h = 1/L`. -/
theorem residualNetwork_flow_error_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (g : ℝ → E → E) (z₀ : E) (K : NNReal)
    (hg : ContDiff ℝ 2 (Function.uncurry g))
    (hlip : ∀ t ∈ Set.Icc (0 : ℝ) 1, LipschitzWith K (g t)) :
    ∃ z : ℝ → E, z 0 = z₀ ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt z (g t (z t)) t) ∧
      ∃ C : ℝ, ∀ L : ℕ, 0 < L → ∀ Z : ℕ → E, Z 0 = z₀ →
        (∀ l : ℕ, Z (l + 1) = Z l + (1 / (L : ℝ)) • g ((l : ℝ) / L) (Z l)) →
          ‖Z L - z 1‖ ≤ C / L := by
  obtain ⟨z, hz0, hz, C, hC⟩ :=
    MathlibExt.Analysis.ODE.ExplicitEulerWanted.explicit_euler_first_order_convergence
      g 0 1 z₀ K zero_lt_one hg hlip
  refine ⟨z, hz0, hz, C, fun L hL Z hZ0 hZ => ?_⟩
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hh : 1 / (L : ℝ) ∈ Set.Ioc 0 (1 - 0) := by
    refine ⟨by positivity, ?_⟩
    rw [sub_zero, div_le_one hL']
    exact_mod_cast hL
  have hstep : ∀ l : ℕ, Z (l + 1) = Z l + (1 / (L : ℝ)) • g (0 + (l : ℝ) * (1 / L)) (Z l) := by
    intro l
    rw [hZ l, zero_add, mul_one_div]
  have hend : (L : ℝ) * (1 / L) = 1 := by field_simp
  have h := hC (1 / L) hh Z hZ0 hstep L (by rw [hend, sub_zero])
  rw [hend, zero_add] at h
  calc ‖Z L - z 1‖ ≤ C * (1 / L) := h
    _ = C / L := mul_one_div C L

end CSLibExt.MachineLearning.NeuralNetworks
