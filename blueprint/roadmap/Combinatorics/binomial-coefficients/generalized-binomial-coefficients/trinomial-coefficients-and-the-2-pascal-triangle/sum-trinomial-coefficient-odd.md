# Generating polynomial of trinomial coefficients with odd index

Write $\binom{n}{k}_2$
for the trinomial coefficient, the coefficient of $t^k$ in $(1+t+t^2)^n$. For every
$n \in \mathbb{N}$ and all complex numbers $z$ and $s$ with $s^2 = z$ and $s \ne 0$

$$\sum_{k=0}^{n} \binom{n}{2k+1}_2 z^k = \frac{(1 + s + z)^n - (1 - s + z)^n}{2s}.$$

The paper states this for an indeterminate $z$, with $\sqrt{z}$ in place of $s$, and calls the
left side $q_n(z)$.

## Sources

- Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of Integer Sequences 28 (2025), Article 25.3.5, Corollary 15 (`jis-2025-25.3.5-cor-15`).
