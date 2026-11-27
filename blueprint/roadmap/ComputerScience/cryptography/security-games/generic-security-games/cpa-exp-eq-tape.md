# The CPA experiment, eagerly sampled

Let the key space $K$, the adversary's coin space $R$ and the encryption randomness space $\mathsf{Rnd}$ be finite and nonempty. Let $S$ be a private-key encryption scheme whose key generation is uniform on $K$ and whose encryption of $m$ under $k$ is the image of the uniform distribution on $\mathsf{Rnd}$ under a deterministic map $u \mapsto e(k, m, u)$. Let $A$ be a CPA adversary whose coins are uniform on $R$ and which makes at most $q$ encryption queries in total along every path (over both stages, and for every challenge ciphertext).

Then for each fixed challenge bit $b$, the output distribution of the left-or-right experiment `cpaExp S A b` equals the law of the [fixed-tape guess](cpa-tape-guess.md)

$$
\mathrm{guess}\bigl(e(k, \cdot, \cdot),\ A.\mathrm{run}(r),\ q,\ \rho,\ r_s,\ b\bigr),
$$

where the key $k \in K$, the coins $r \in R$, the tape $\rho \in \mathsf{Rnd}^q$ and the challenge randomness $r_s \in \mathsf{Rnd}$ are drawn independently and uniformly. In the fixed-tape guess the two stages share the $q$ entries of $\rho$ (the $i$th encryption query uses $\rho_i$), the challenge ciphertext is $e(k, m_b, r_s)$ with the separate entry $r_s$, and a query beyond the $q$ tape entries makes the guess `false`.

This is an equality of distributions on Booleans, not a statement that `cpaExp` itself samples its randomness up front.
