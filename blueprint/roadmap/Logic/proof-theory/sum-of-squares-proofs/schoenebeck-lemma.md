# Schoenebeck's lemma: width lower bounds give SOS pseudo-expectations for parity

Let $P$ be a parity system over $\pm 1$ variables, and suppose $0 = 1$ has no width-$d$ derivation from $P$. Then the $\pm1$ encoding of $P$ has a degree-$d$ pseudo-expectation: set $\tilde{\mathbb{E}}[\prod_{i\in S} x_i] = (-1)^b$ if $\bigoplus_{i \in S} x_i = b$ is derivable in width $d$, and $0$ otherwise. Consequently $P$ has no SOS refutation of degree at most $d$.

## Proof sketch

Derivable equations of small width are consistent (no two derive opposite right-hand sides), so the functional is well defined; positivity on squares reduces to a block-diagonal decomposition into equivalence classes of monomials modulo derivable equations, each block being a rank-one positive semidefinite matrix.

## Depends on

- [Parity systems and bounded-width derivations](parity-systems-and-bounded-width-derivations.md)
- [Degree-$d$ pseudo-expectations](pseudo-expectations.md)

## Sources

- G. Schoenebeck, "Linear Level Lasserre Lower Bounds for Certain k-CSPs", Proceedings of the 49th IEEE Symposium on Foundations of Computer Science (FOCS), 2008.
- D. Grigoriev, "Linear Lower Bound on Degrees of Positivstellensatz Calculus Proofs for the Parity", Theoretical Computer Science 259(1–2), 613–622, 2001.
