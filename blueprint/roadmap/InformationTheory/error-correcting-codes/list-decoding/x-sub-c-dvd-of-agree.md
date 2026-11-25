# $Y - P(X)$ divides the interpolating polynomial

Under the hypotheses of the [root-finding lemma](eval-eq-zero-of-agree.md), $Y - P(X)$ divides
$Q(X, Y)$ in $F[X][Y]$. So Step 3 of the Guruswami–Sudan algorithm, which factors $Q$ and keeps
the factors $Y - P(X)$ with $\deg P < k$ close to the received word, finds every polynomial that
agrees with the received word in $t$ positions with $D < t r$.

## Informally uses

- [Guruswami–Sudan root-finding lemma](eval-eq-zero-of-agree.md): $Q(X, P(X)) = 0$, then the factor theorem in $F[X][Y]$.

## Sources

- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Algorithm 12.2.3 and Lemma 12.2.13.
