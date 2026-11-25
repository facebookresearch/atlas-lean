# Arrowhead entries along the equilibrium branch

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
[`β_n`](../hodgkin-huxley-model/beta-n.md), and `α_m'` the derivative of `α_m` (taken as `0` at a
point where it does not exist), and so on. They form the [arrowhead matrix](mat.md) at `V`.
