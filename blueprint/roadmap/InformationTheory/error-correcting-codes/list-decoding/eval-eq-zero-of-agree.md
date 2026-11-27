# Guruswami–Sudan root-finding lemma

Let $\alpha_1, \dots, \alpha_n \in F$ be distinct and $y \in F^n$. Let $Q \in F[X][Y]$ have
[$(1, w)$-weighted degree](weighted-deg-le.md) at most $D$ and a
[root of multiplicity](has-root-mult.md) at least $r$ at every point $(\alpha_i, y_i)$. If
$P \in F[X]$ has degree at most $w$ and $P(\alpha_i) = y_i$ for $t$ indices $i$ with $t r > D$,
then $Q(X, P(X)) = 0$; equivalently [$Y - P(X)$ divides $Q$](x-sub-c-dvd-of-agree.md).

Indeed $R(X) = Q(X, P(X))$ has degree at most $D$, while $(X - \alpha_i)^r$ divides $R$ for each
of the $t$ agreeing indices, so $R$ is divisible by a polynomial of degree $t r > D$.

This is Lemma 12.2.13 of Guruswami, Rudra and Sudan with $w = k - 1$, stated there for the
polynomial found by the interpolation step of their Algorithm 12.2.3; only its weighted-degree and
multiplicity properties are used, so the lemma holds for every such $Q$. It is the
root-finding half of the [Guruswami–Sudan list decoder](exists-interpolant-dvd.md) for
Reed–Solomon codes; the other half is the [interpolation step](exists-interpolant.md).

## Informally uses

- [Substitution respects the weighted degree](nat-degree-eval-le.md): $\deg R \le D$ (Lemma 12.2.6).
- [A root of multiplicity $r$ survives substitution](pow-dvd-eval-of-has-root-mult.md): Claim 12.2.14.

## Background

- [Root count at distinct points](../reed-solomon-codes/card-eval-eq-zero-le.md): the "degree mantra" (Proposition 5.1.5) that the source's proof invokes; the argument above counts the roots with multiplicity instead.

## Sources

- V. Guruswami, M. Sudan, "Improved decoding of Reed–Solomon and algebraic-geometry codes", *IEEE Transactions on Information Theory* 45(6) (1999), 1757–1767.
- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Algorithm 12.2.3 and Lemma 12.2.13.
