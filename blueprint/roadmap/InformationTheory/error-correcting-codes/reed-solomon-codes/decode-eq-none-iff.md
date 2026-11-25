# The decoder fails exactly when no codeword is close

Let $F$ be a field, let
$\alpha_0, \dots, \alpha_{n-1} \in F$ be pairwise distinct, let $k, e$ be natural numbers
with $2e + k \le n$, and let $S$ be a solver for the key equations with error budget $e$.
For every received word $y \in F^n$, the Berlekamp-Welch decoder with solver $S$ reports
failure on $y$ if and only if, for every polynomial $p \in F[X]$ of degree less than $k$, the
Hamming distance between $y$ and $(p(\alpha_0), \dots, p(\alpha_{n-1}))$ is greater than $e$.
