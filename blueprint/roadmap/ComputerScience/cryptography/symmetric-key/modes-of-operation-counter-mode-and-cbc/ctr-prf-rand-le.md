# Counter-mode reduction against a random function

Let $N > 0$, $\ell \le N$, let $Y$ be a finite nonempty additive commutative group, and let the adversary's coin space $R$ be finite and nonempty. For every CPA adversary against counter mode with $\ell$-block messages and every $q \in \mathbb{N}$, run the [counter-mode reduction](ctr-reduction.md) with tape length $q$ in the random world: the oracle is a uniformly random function $f \colon \mathbb{Z}/N \to Y$ and the reduction's coins $(b, r, \rho, r_s) \in \mathrm{Bool} \times R \times (\mathbb{Z}/N)^q \times \mathbb{Z}/N$ are uniform and independent of $f$. Then

$$
\Bigl|\Pr[\text{the reduction outputs true}] - \tfrac12\Bigr| \le \frac{q \cdot \max(2\ell - 1, 0)}{2N}.
$$

This inequality is unconditional: it needs neither a query bound nor uniform adversary coins. On a fixed coin tuple the reduction outputs whether the [fixed-tape guess](../../security-games/generic-security-games/cpa-tape-guess.md) with encryption $\mathrm{ctrEncrypt}(f, \cdot, \cdot)$ equals $b$, and a query beyond the tape makes that guess `false`. The proof uses the separate exact count that, for fixed $(r, \rho, r_s)$ with a fresh challenge range, this guess equals $b$ for [exactly half the pairs](ctr-two-mul-card-wins.md) $(f, b)$, together with the [count of non-fresh challenge counters](card-not-ctr-fresh.md).
