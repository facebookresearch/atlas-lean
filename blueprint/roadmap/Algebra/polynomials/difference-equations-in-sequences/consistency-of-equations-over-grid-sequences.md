# Consistency of equations over sequences indexed by the plane grid is undecidable

Over a field of characteristic zero, no algorithm decides whether a finite system of equations with two commuting shifts, with coefficients in a computable subfield, has a solution in sequences indexed by $\mathbb{Z}^2$, or by $\mathbb{N}^2$.

**Theorem (Pogudin–Scanlon–Wibmer).** Let $k$ be a field of characteristic zero, let $k_0 \subseteq k$ be a computable subfield, and let $M$ be $\mathbb{N}^2$ or $\mathbb{Z}^2$ (under addition). There is no algorithm that decides, given a finite set $F$ of $M$-polynomials in finitely many unknowns with coefficients in $k_0$, whether the system $F = 0$ has a solution in $k^M$.

Conventions: $k^M$ is the ring of sequences $(x_{i,j})$ indexed by $M$ with the shifts $\sigma^{(1,0)}$ and $\sigma^{(0,1)}$ (and their inverses for $\mathbb{Z}^2$), as in the linked definitions. For $M = \mathbb{N}$ or $\mathbb{Z}$ the same question is undecidable for $k \subseteq \mathbb{R}$ by a separate argument; for one-sided sequences $K^{\mathbb{N}}$ over an algebraically closed difference field $K$ it is decidable, by the effective bound of Ovchinnikov, Pogudin and Scanlon that the source recalls.

## Depends on

- [Difference rings and rings of sequences](difference-rings-and-equations-in-sequences.md)
- [Difference polynomials and their solutions](difference-polynomials-and-their-solutions.md)
- [Computable subfields](computable-subfields.md)
- [Field](../../rings-and-fields/field.md)
- [Predicates decidable by a single-tape Turing machine](../../../TheoryOfComputation/turing-machines/single-tape/decidable-and-recognizable-predicates-on-single/single-tape-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

For $M = \mathbb{Z}^2$ the proof encodes Berger's tiling problem. Given a finite set of tiles $D_1, \dots, D_n$ whose edge colors are integers $1, \dots, N$, with $D_s(b), D_s(t), D_s(l), D_s(r)$ the colors of the bottom, top, left and right edges, let $x_{i,j}$ be the color of the horizontal edge from $(i, j)$ to $(i+1, j)$ and $y_{i,j}$ that of the vertical edge from $(i, j)$ to $(i, j+1)$, and take

$$
\prod_{c=1}^{N} (X - c) = 0, \qquad \prod_{c=1}^{N} (Y - c) = 0,
$$

$$
\prod_{s=1}^{n} \Bigl( (D_s(b) - X)^2 + (D_s(t) - \sigma^{(0,1)}(X))^2 + (D_s(l) - Y)^2 + (D_s(r) - \sigma^{(1,0)}(Y))^2 \Bigr) = 0 .
$$

The first two equations force integer colors, and since the colors are integers the last one holds exactly when every unit square carries one of the tiles; so the solutions in $k^{\mathbb{Z}^2}$ are exactly the tilings of the plane. For $M = \mathbb{N}^2$ the source shows that this particular system has a solution in $k^{\mathbb{N}^2}$ exactly when it has one in $k^{\mathbb{Z}^2}$: restriction gives one direction, and if there is no solution over $\mathbb{Z}^2$, the strong Nullstellensatz over an uncountable algebraically closed field gives an identity $1 = \sum c_{i,j} \sigma^{(i,j)}(f)$ with shifts bounded by some $H$, which can be shifted into $\mathbb{N}^2$.

A good expansion adds and links pages for the comparison of solutions over $\mathbb{N}^2$ and $\mathbb{Z}^2$ for this system and for the strong Nullstellensatz for difference equations over an uncountable algebraically closed field.

## Sources

- Gleb Pogudin, Thomas Scanlon and Michael Wibmer, *Solving difference equations in sequences: universality and undecidability*, Forum of Mathematics, Sigma 8 (2020), e33, https://doi.org/10.1017/fms.2020.14; Proposition 3.9 of arXiv:1909.03239v2, proved in Section 4.4 there (with Lemma 4.10 for $\mathbb{N}^2$).
- Robert Berger, *The undecidability of the domino problem*, Memoirs of the American Mathematical Society 66 (1966), https://doi.org/10.1090/memo/0066, for the tiling problem the proof reduces from, as cited in the paper above.
