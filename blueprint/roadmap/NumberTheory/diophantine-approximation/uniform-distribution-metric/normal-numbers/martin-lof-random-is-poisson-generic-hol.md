# Martin-Löf random sequences are Poisson generic

Every Martin-Löf random binary sequence is Poisson generic, where a binary sequence $x$ is Poisson generic when for every real $\lambda > 0$ and every $k \ge 0$, the proportion of the $2^n$ binary words $w$ of length $n$ occurring exactly $k$ times in $x$ at positions $i < \lfloor \lambda 2^n \rfloor$ tends to $e^{-\lambda}\lambda^k/k!$ as $n \to \infty$, and a binary sequence $x$ is Martin-Löf random when for every Martin-Löf test $U$, a uniformly computably enumerable sequence $U_0, U_1, \dots$ of sets of finite binary strings such that the sequences with a prefix in $U_m$ have fair-coin measure at most $2^{-m}$, some $U_m$ contains no prefix of $x$.

This resolves [Becher's question on random Poisson generic sequences](martin-lof-random-is-poisson-generic.md), the statement recorded as a proposition, in the affirmative; the resolution is due to Álvarez, Becher and Mereb (2023), cited under Sources.

## Sources

- V. Becher, open problems, Computability Theory, Oberwolfach Report 21/2021, p. 1179.
- N. Álvarez, V. Becher and M. Mereb, Poisson generic sequences, Int. Math. Res. Not. IMRN 2023, no. 24, 20970–20987, arXiv:2202.01632, https://doi.org/10.1093/imrn/rnac234. Theorem 3.
