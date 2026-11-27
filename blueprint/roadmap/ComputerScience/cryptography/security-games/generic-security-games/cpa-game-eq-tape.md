# The CPA game, eagerly sampled

Let the key space $K$, the adversary's coin space $R$ and the encryption randomness space $\mathsf{Rnd}$ be finite and nonempty. Let $S$ be a private-key encryption scheme whose key generation is uniform on $K$ and whose encryption of $m$ under $k$ is the image of the uniform distribution on $\mathsf{Rnd}$ under a deterministic map $u \mapsto e(k, m, u)$. Let $A$ be a CPA adversary whose coins are uniform on $R$ and which makes at most $q$ encryption queries in total along every path.

Then the CPA game of $S$ against $A$, a distribution on Booleans, equals the pushforward of the uniform distribution on $K \times \mathrm{Bool} \times R \times \mathsf{Rnd}^q \times \mathsf{Rnd}$ under the test

$$
(k, b, r, \rho, r_s) \mapsto \bigl[\mathrm{guess}(e(k, \cdot, \cdot), A.\mathrm{run}(r), q, \rho, r_s, b) = b\bigr],
$$

where $\mathrm{guess}$ is the [fixed-tape guess](cpa-tape-guess.md). Only the mass of this distribution at `true` is the probability that $A$ wins.
