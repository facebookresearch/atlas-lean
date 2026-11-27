# Poincaré–Birkhoff–Witt theorem

This node is still to be broken down. It covers the Poincaré–Birkhoff–Witt theorem and its corollaries, which the pages
on distributions on Lie groups, on $(\mathfrak{g}, K)$-modules and on the Hecke algebra of a real reductive group use. Let
$\mathfrak{g}$ be a Lie algebra over a field $k$ and $U(\mathfrak{g})$ its
[universal enveloping algebra](universal-enveloping-algebra.md), filtered by degree.

- **Theorem.** The natural surjection $S(\mathfrak{g}) \to \operatorname{gr} U(\mathfrak{g})$ from the symmetric algebra is an isomorphism;
  equivalently, for an ordered basis $(x_i)$ of $\mathfrak{g}$, the ordered monomials $\prod_i x_i^{n_i}$ form a basis of $U(\mathfrak{g})$.
  In particular $\mathfrak{g} \to U(\mathfrak{g})$ is injective, and if $\mathfrak{g} = \bigoplus_i \mathfrak{g}_i$ as a vector space for Lie
  subalgebras $\mathfrak{g}_1, \dots, \mathfrak{g}_n$, multiplication $\bigotimes_i U(\mathfrak{g}_i) \to U(\mathfrak{g})$, in any order, is a linear
  isomorphism.
- **Symmetrization.** If $k$ has characteristic zero, the symmetrization map $S(\mathfrak{g}) \to U(\mathfrak{g})$,
  $y_1 \cdots y_n \mapsto \frac{1}{n!} \sum_{s \in S_n} y_{s(1)} \cdots y_{s(n)}$, is a linear isomorphism commuting with the adjoint
  action of $\mathfrak{g}$, and it restricts to a filtered linear isomorphism from $S(\mathfrak{g})^{\mathrm{ad}\, \mathfrak{g}}$ onto the centre of
  $U(\mathfrak{g})$.

## Expansion

A good expansion has statement pages for the theorem in its graded and basis forms, for the decomposition along a direct
sum of subalgebras, and for the symmetrization map and the centre, each citing the source below with locators.

## Depends on

- [Universal enveloping algebra of a Lie algebra](universal-enveloping-algebra.md), for $U(\mathfrak{g})$ and its filtration

## Proof depends on

Its proof is that of the source below, as the Expansion describes.

## Sources

- P. Etingof, "Lie groups and Lie algebras", lecture notes, arXiv:2201.09397 (version 5), <https://arxiv.org/abs/2201.09397>:
  §13.1, Theorem 13.1 and Theorem 13.2 (the Poincaré–Birkhoff–Witt theorem, graded and basis forms), Corollaries 13.3
  and 13.5 (injectivity of $\mathfrak{g} \to U(\mathfrak{g})$ and the decomposition along subalgebras), and Corollaries 13.7 and 13.8
  (symmetrization and the centre), pp. 69–70, with the proof in §13.2.
