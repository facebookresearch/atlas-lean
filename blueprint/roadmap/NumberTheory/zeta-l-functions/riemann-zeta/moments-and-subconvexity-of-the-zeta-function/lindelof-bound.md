# Lindelöf bound for the Riemann zeta function

For every real $\varepsilon > 0$ there are real constants $C$ and $t_0$ such that

$$
|\zeta(\sigma + it)| \le C |t|^{\varepsilon}
$$

for all real $\sigma$ and $t$ with $1/2 \le \sigma \le 1$ and $|t| \ge t_0$. On the critical line
this is the Lindelöf hypothesis, $\zeta(1/2 + it) = O(|t|^{\varepsilon})$.

It follows from the Riemann hypothesis by the conditional bound of the same form.

## Proof depends on

- [Riemann hypothesis](../zeros-of-the-riemann-zeta-function/riemann-hypothesis.md)
- [Lindelöf bound from the Riemann hypothesis](../../../arithmetic-functions/special-integer-classes/mean-value-of-2-n-over-squareful-numbers/zeta-le-rpow-of-riemann-hypothesis.md)

## Sources

- Kampamolla Venkatasubbareddy and Ayyadurai Sankaranarayanan, *On the Distribution of the Restricted Sequence of Integers 2^{ω(n)}*, INTEGERS 24 (2024), Article A110, Lemma 8, for the bound under the Riemann hypothesis.
- Proof of the Riemann hypothesis: L. Alpöge, released 2026-11-20 as a Lean library (<https://alpo.ge/remark.pdf>). The Lean and Mathlib communities certified the statement and the proof of the Riemann hypothesis in a joint statement of 2026-11-21 endorsed by the Lean FRO and the Mathlib Initiative (<https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>); independent checks by A. Sutherland (<https://math.mit.edu/~drew/grh/>). Source mirror: <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>.
