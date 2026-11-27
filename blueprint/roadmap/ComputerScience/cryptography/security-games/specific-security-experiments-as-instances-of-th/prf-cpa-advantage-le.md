# CPA security of PRF-based encryption

Let the key space $K$, the randomness space $X$ and the adversary's coin space $R$ be finite and nonempty, let $X$ have decidable equality, and let $Y$ be a finite additive commutative group. Let $F \colon K \to X \to Y$ and let $A$ be a coin-indexed CPA adversary such that its [uniform-coin embedding](to-cpaadversary.md) makes at most $q$ encryption queries in total along every path. Then the CPA advantage $|\Pr[\mathrm{PrivK}^{\mathrm{cpa}} = 1] - 1/2|$ of the embedded adversary against the [PRF-based scheme](prf-enc.md) satisfies

$$
\mathrm{Adv}^{\mathrm{cpa}} \le \mathrm{Adv}^{\mathrm{prf}}_F(\mathrm{cpaReduction}_q(A)) + \frac{q}{2|X|},
$$

where $\mathrm{cpaReduction}_q(A)$ is the PRF distinguisher that simulates the encryption oracle with its own up-front randomness (Katz and Lindell, Theorem 3.31).
