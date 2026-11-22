# Franel's bound for the discrepancy of Farey sequences

For a natural number $N$, let $F_N(0) < F_N(1) < \dots < F_N(L_N - 1)$ be the terms of the Farey
sequence of order $N$, and for $k < L_N$ let $\delta_{N,k} = F_N(k) - k/(L_N - 1)$. For every real
$\varepsilon > 0$,

$$
\sum_{k=0}^{L_N - 1} \delta_{N,k}^2 = O\bigl(N^{-1 + \varepsilon}\bigr) \quad (N \to \infty).
$$

This is the Riemann hypothesis read through the Franel–Landau theorem, which states that the
Riemann hypothesis holds if and only if the bound holds for every $\varepsilon > 0$.

## Proof depends on

- [Riemann hypothesis](zeros-of-the-riemann-zeta-function/riemann-hypothesis.md)
- [Franel–Landau theorem](franel-landau.md)

## Sources

- J. Franel, *Les suites de Farey et le problème des nombres premiers*, Nachr. Ges. Wiss. Göttingen, Math.-Phys. Kl. 1924, 198–201, for the equivalence, as stated in the Wikipedia article "Farey sequence", section "Riemann hypothesis", <https://en.wikipedia.org/wiki/Farey_sequence>.
- Proof of the Riemann hypothesis: L. Alpöge, released 2026-11-20 as a Lean library (<https://alpo.ge/remark.pdf>). The Lean and Mathlib communities certified the statement and the proof of the Riemann hypothesis in a joint statement of 2026-11-21 endorsed by the Lean FRO and the Mathlib Initiative (<https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>); independent checks by A. Sutherland (<https://math.mit.edu/~drew/grh/>). Source mirror: <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>.
