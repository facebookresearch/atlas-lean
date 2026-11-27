# The fixed-tape PRF-encryption guess as one run

Let $Y$ be an additive commutative group, $f \colon X \to Y$, $\rho \in X^q$ the encryption randomness, $r_s \in X$ the challenge randomness, $b$ a bit, and $c$ a two-stage oracle computation whose first stage returns messages $(m_0, m_1)$ and a second stage taking a ciphertext in $X \times Y$ to a Boolean. Then the PRF file's fixed-tape guess $\mathrm{cpaGuess}(f, \rho, r_s, b, c)$ is obtained as follows: compose $c$ with the continuation that passes the challenge $(r_s, f(r_s) + m_b)$ to the second stage; run this composed computation with $\mathrm{runEnc}$ from index $0$; on success project out the resulting bit, and on failure of either stage return `false`.

Here $\mathrm{runEnc}$ runs an oracle computation against the encryption oracle with up-front randomness $\rho \in X^q$, starting from a query index $i$: a returned value $a$ gives `some` $(a, i)$; a query $m$ with $i < q$ is answered by $(\rho_i, f(\rho_i) + m)$ and the run continues from index $i + 1$; a query with $i \ge q$ makes the run fail (`none`).

This is a pointwise equation; it needs no finiteness or query-bound hypothesis.
