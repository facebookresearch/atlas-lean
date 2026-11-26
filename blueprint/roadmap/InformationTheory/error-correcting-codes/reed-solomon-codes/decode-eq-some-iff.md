# What the decoder returns

Let $F$ be a field, let $\alpha_0, \dots, \alpha_{n-1} \in F$
be pairwise distinct, let $k, e$ be natural numbers with $2e + k \le n$ (the unique-decoding
regime), and let $S$ be a solver for the key equations with error budget $e$. For every
polynomial $p \in F[X]$ and every received word $y \in F^n$, the Berlekamp-Welch decoder with
solver $S$ returns $p$ on $y$ if and only if $p$ has degree less than $k$ and the Hamming
distance between $y$ and $(p(\alpha_0), \dots, p(\alpha_{n-1}))$ is at most $e$.
