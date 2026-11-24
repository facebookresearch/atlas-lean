# Polynomial growth is independent of the finite generating set

For two finite generating families $P$ and $Q$ of a group $G$, $P$ has polynomial growth if and only if $Q$ does. Polynomial growth is therefore a property of the finitely generated group: Gromov's remark that "this definition does not depend on the particular choice of the generators and so this notion is correctly defined for the finitely generated groups".

The balls of radius $n$ for $P$ lie in the balls of radius $K n$ for $Q$, with $K$ the bi-Lipschitz constant of the word metrics, so $\gamma_P(n) \le \gamma_Q(Kn) \le C (Kn + 1)^d \le C (K + 1)^d (n + 1)^d$.

## Background

- [Change of finite generating set is bi-Lipschitz](../word-metrics-and-quasi-isometries/exists-word-length-bilipschitz.md): the two-sided comparison of word lengths behind the argument (one direction of it suffices, applied twice).

## Sources

- M. Gromov, *Groups of polynomial growth and expanding maps*, Publ. Math. IHÉS 53 (1981), 53–73, p. 54.
