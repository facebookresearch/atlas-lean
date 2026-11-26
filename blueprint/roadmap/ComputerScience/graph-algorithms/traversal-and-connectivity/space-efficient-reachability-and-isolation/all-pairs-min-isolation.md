# Some seed min-isolates every layered digraph

Let the code $\gamma$ of Hoza's seeded weight family have length $\ell$ and minimum distance $d$. Then for every layered digraph $G$ on $\{0,\dots,n\} \times \{0, \dots, w-1\}$, at most $2^{\ell-d} n^2 w^4$ seeds $z \in \{0,1\}^\ell$ fail to make $\mathrm{wt}_z$ min-isolating for $G$ (Hoza, Theorem 2.4); hence if $2^d > n^2 w^4$, some seed $z$ makes $\mathrm{wt}_z$ min-isolating for all reachable pairs of $G$ simultaneously. Binary codes with $w$ codewords, $d = \Theta(\log(nw))$ and $\ell = O(\log(nw))$ exist (for example Justesen codes), and with such a code every weight $\mathrm{wt}_z(i, c)$ is bounded by a polynomial in $n w$.

## Proof sketch

Union bound: a non-isolating seed creates a tie between two minimum-weight path families that first differ at some dominant layer; there are polynomially many (pair, interval, two columns) events, each with at most $2^{\ell-d}$ tying seeds, since two distinct codewords agree on at most $\ell - d$ positions.

## Depends on

- [Hoza's seeded weight family](hoza-seeded-weight-family.md)

## Proof depends on

- [Few seeds tie two path families](tying-seed-bound.md)

## Sources

- W. M. Hoza, "NL = UL", Electronic Colloquium on Computational Complexity, Report TR26-323, 2026.
