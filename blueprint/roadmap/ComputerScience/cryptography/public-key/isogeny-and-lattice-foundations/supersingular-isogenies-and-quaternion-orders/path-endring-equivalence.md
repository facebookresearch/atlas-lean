# Equivalence of the isogeny path and endomorphism ring problems

Assuming the generalized Riemann hypothesis, the supersingular $\ell$-isogeny path problem and the endomorphism ring problem are equivalent under probabilistic polynomial-time reductions (in $\log p$). Moreover, both are equivalent to the problem of computing, given $E$, an efficient representation of $\mathrm{End}(E)$ via the maximal order $\mathcal{O}\subseteq B_{p,\infty}$ isomorphic to it, and they are polynomially equivalent to the one-endomorphism problem in a suitable sense (subsequent work). Consequently the security of isogeny path based schemes rests on the hardness of computing endomorphism rings.

## Proof sketch

From an endomorphism ring of both curves, find the connecting ideal and convert it to an $\ell$-power path with a rigorous version of KLPT (made unconditional up to GRH by analyzing the distribution of norms). Conversely, given a path oracle, random walks from $E$ and loops closing at $E$ produce endomorphisms; enough random endomorphisms generate $\mathrm{End}(E)$ with good probability, by equidistribution arguments using GRH.

## Depends on

- [The supersingular isogeny path and endomorphism ring problems](isogeny-path-and-endring-problems.md)
- [The quaternion algebra ramified at p and infinity and its maximal orders](quaternion-algebra-bp.md)

## Proof depends on

- [KLPT: ideals of powersmooth or prime-power norm in a special maximal order](klpt-algorithm.md)
- [Supersingular isogeny graphs are Ramanujan and random walks mix rapidly](isogeny-graph-ramanujan.md)

## Sources

- Benjamin Wesolowski, "The Supersingular Isogeny Path and Endomorphism Ring Problems are Equivalent", FOCS (2021), arXiv:2111.01481.
