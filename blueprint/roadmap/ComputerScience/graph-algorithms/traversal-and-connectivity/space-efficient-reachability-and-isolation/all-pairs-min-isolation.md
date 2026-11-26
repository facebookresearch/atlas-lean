# Some seed min-isolates every layered digraph

With a code of relative distance large enough that any two codewords agree on at most a constant fraction of positions, and a seed length $\ell = O(\log(nw))$, for every layered digraph $G$ on $\{0,\dots,n\} \times \{0, \dots, w-1\}$ the number of seeds that fail to min-isolate $G$ is less than $2^{\ell}$; hence some seed $z$ makes $\mathrm{wt}_z$ min-isolating for all reachable pairs of $G$ simultaneously. The resulting weights are bounded by a polynomial in $n w$.

## Proof sketch

Union bound: a non-isolating seed creates a tie between two minimum-weight path families that first differ at some dominant layer; there are polynomially many (pair, interval, two columns) events, each with at most $2^{a}$ tying seeds, and the code distance makes their total smaller than the seed space.

## Depends on

- [Hoza's seeded weight family](hoza-seeded-weight-family.md)

## Proof depends on

- [Few seeds tie two path families](tying-seed-bound.md)

## Sources

- W. M. Hoza, "NL = UL", Electronic Colloquium on Computational Complexity, Report TR26-323, 2026.
