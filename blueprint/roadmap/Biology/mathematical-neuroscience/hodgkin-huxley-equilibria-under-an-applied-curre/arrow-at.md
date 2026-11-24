# Arrowhead entries of the squid Jacobian along the equilibrium branch

For real `V`, write `m = m∞(V)`, `h = h∞(V)` and `n = n∞(V)` for the steady-state gating values
[`m∞`](../hodgkin-huxley-model/m-inf.md), [`h∞`](../hodgkin-huxley-model/h-inf.md) and
[`n∞`](../hodgkin-huxley-model/n-inf.md). The [arrowhead entries](arrow.md) at `V` are

- `a = -(120 m³ h + 36 n⁴ + 0.3)`;
- `b₁ = 360 m² h (115 - V)`, `b₂ = 120 m³ (115 - V)` and `b₃ = -144 n³ (V + 12)`;
- `c₁ = α_m'(V) (1 - m) - β_m'(V) m`, `c₂ = α_h'(V) (1 - h) - β_h'(V) h` and
  `c₃ = α_n'(V) (1 - n) - β_n'(V) n`;
- `k₁ = α_m(V) + β_m(V)`, `k₂ = α_h(V) + β_h(V)` and `k₃ = α_n(V) + β_n(V)`,

with the Hodgkin–Huxley rate functions [`α_m`](../hodgkin-huxley-model/alpha-m.md),
[`β_m`](../hodgkin-huxley-model/beta-m.md), [`α_h`](../hodgkin-huxley-model/alpha-h.md),
[`β_h`](../hodgkin-huxley-model/beta-h.md), [`α_n`](../hodgkin-huxley-model/alpha-n.md) and
[`β_n`](../hodgkin-huxley-model/beta-n.md), which are positive and continuously differentiable on
`ℝ`, and their derivatives. So `k₁, k₂, k₃ > 0`. Their [arrowhead matrix](mat.md) is the
[Jacobian](../hodgkin-huxley-model/jac.md) of the squid Hodgkin–Huxley field at the
[branch point](eq-point.md) `(V, m, h, n)`. The applied current `I` enters the squid vector field
only as the constant term of its voltage component `I - I_ion(V, m, h, n)` (here `C = 1`), so this
Jacobian is the same for every applied current.
