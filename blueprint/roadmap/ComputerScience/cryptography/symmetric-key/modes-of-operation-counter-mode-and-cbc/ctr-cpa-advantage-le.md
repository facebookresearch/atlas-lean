# Concrete CPA advantage bound for counter mode

Let $N > 0$, $\ell \le N$, let $Y$ be a finite nonempty additive commutative group, and let the key space $K$ and the adversary's coin space $R$ be finite and nonempty. For every keyed function $F \colon K \to \mathbb{Z}/N \to Y$ and every CPA adversary against [counter mode](ctr-scheme.md) with $\ell$-block messages whose coins are uniform on $R$ and which makes at most $q$ encryption queries in total along every path,

$$
\mathrm{Adv}^{\mathrm{cpa}} \le \mathrm{Adv}^{\mathrm{prf}}_F(\mathrm{ctrReduction}_q) + \frac{q \cdot \max(2\ell - 1, 0)}{2N},
$$

where the CPA advantage is $|\Pr[\mathrm{PrivK}^{\mathrm{cpa}} = 1] - 1/2|$ and $\mathrm{ctrReduction}_q$ is the [PRF distinguisher](ctr-reduction.md) built from the adversary.

This is a concrete estimate for a single adversary. Katz and Lindell, 2nd ed., Theorem 3.32 (p. 93) states the asymptotic implication that counter mode is CPA-secure when $F$ is a pseudorandom function; the numerical error term above is a concrete estimate for this construction, not part of that statement.
