# Schoenebeck's lemma: width lower bounds give SOS pseudo-expectations for parity

Let $P$ be a parity system and suppose $0 = 1$ has no width-$w$ derivation from $P$. Then round $\lfloor w/4 \rfloor$ of the Lasserre hierarchy for $P$ is feasible; in the language of pseudo-expectations, the $\pm 1$ encoding of $P$ has a pseudo-expectation of degree $d = 2\lfloor w/4 \rfloor$, given on monomials of degree at most $d$ by $\tilde{\mathbb{E}}[\prod_{i\in S} x_i] = (-1)^b$ if $\bigoplus_{i \in S} x_i = b$ is derivable in width $w$, and $0$ otherwise. Consequently $P$ has no SOS refutation of degree at most $d$.

## Proof sketch

Since $0 = 1$ is not derivable, no two width-$w$ derivations give opposite right-hand sides for the same set, so the values are well defined. Group the sets of at most $w/2$ variables into classes $I \sim J$ when $\bigoplus_{I \triangle J} x_i$ is fixed by a width-$w$ derivation; the Lasserre vectors for assignments to at most $w/4$ variables are built coordinatewise from these classes with signs given by the derived equations, and the moment matrix is block diagonal with rank-one positive semidefinite blocks.

## Depends on

- [Parity systems and bounded-width derivations](parity-systems-and-bounded-width-derivations.md)
- [Degree-$d$ pseudo-expectations](pseudo-expectations.md)

## Sources

- G. Schoenebeck, "Linear Level Lasserre Lower Bounds for Certain k-CSPs", Proceedings of the 49th IEEE Symposium on Foundations of Computer Science (FOCS), 2008: Lemma 13 (Main Lemma) and its proof.
- D. Grigoriev, "Linear Lower Bound on Degrees of Positivstellensatz Calculus Proofs for the Parity", Theoretical Computer Science 259(1–2), 613–622, 2001.
