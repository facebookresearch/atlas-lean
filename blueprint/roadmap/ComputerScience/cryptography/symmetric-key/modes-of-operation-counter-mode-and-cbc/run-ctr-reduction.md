# Run ctr Reduction

Let $Y$ be an additive commutative group. For every CPA adversary against counter mode with $\ell$-block messages, every $q$, every function $f \colon \mathbb{Z}/N \to Y$ and every fixed coin tuple $(b, r, \rho, r_s)$ with $\rho \in (\mathbb{Z}/N)^q$, running the [counter-mode reduction](ctr-reduction.md) against $f$ returns

$$
\bigl[\mathrm{guess}(\mathrm{ctrEncrypt}(f, \cdot, \cdot), A.\mathrm{run}(r), q, \rho, r_s, b) = b\bigr],
$$

where $\mathrm{guess}$ is the [fixed-tape guess](../../security-games/generic-security-games/cpa-tape-guess.md): the two stages share the $q$ counters of $\rho$, the challenge uses the separate counter $r_s$, and a query beyond the tape makes the guess `false`. This is a pointwise equation; it needs no uniform-coin or query-bound hypothesis.
