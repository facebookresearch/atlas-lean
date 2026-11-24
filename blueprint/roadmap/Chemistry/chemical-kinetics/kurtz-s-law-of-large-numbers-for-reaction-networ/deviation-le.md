# Kurtz's pathwise estimate

**Kurtz's pathwise estimate** (Kurtz 1970; Ethier–Kurtz 1986, ch. 11, proof of Thm 2.1),
localized to the `δ`-tube around the deterministic trajectory. Let `X` be a chain path of a
network with propensities `λ_r` and `x` a solution of the mean-field equation `x' = ∑_r β_r(x) ζ_r`.
Suppose that on the `δ`-tube around `x` over `[0, T]`

* the scaled propensities are close to `β` along the trajectory,
  `|λ_r(z) / N - β_r(x(s))| ≤ e + L ‖z / N - x(s)‖₁`, and bounded by `B`, and
* the scaled clocks are within `η` of the identity on `[0, (B + 1) T]`,
  `|y_r(N a) / N - a| ≤ η`.

With `Z = ∑_r ‖ζ_r‖₁` and `A = dev(0) + Z (η + e T)`, if `A e^{L Z T} + 2 η Z < δ` then

`‖X(t) / N - x(t)‖₁ ≤ A e^{L Z t}` for all `t ∈ [0, T]`.

Proof: let `t₀` be the supremum of the times before which the path stays in the tube. Gronwall's
inequality bounds the deviation by `A e^{L Z t}` on `[0, t₀]`; if `t₀ < T`, the bounded jumps and
continuity of the clocks keep the path in the tube a little longer, a contradiction.
