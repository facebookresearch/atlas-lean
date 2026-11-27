# The first-order theory of the field of rational numbers is undecidable

The set of first-order sentences in the language of rings that are true in the field $\mathbb{Q}$ of rational numbers is not computable: no algorithm decides, for a sentence built from $+$, $\cdot$, $0$, $1$, equality, connectives and quantifiers over $\mathbb{Q}$, whether it holds in $\mathbb{Q}$.

Let $\mathcal{L}_{\mathrm{ring}} = \{+, \cdot, 0, 1\}$ be the language of rings, with equality, and let $\operatorname{Th}(\mathbb{Q})$ be the complete theory of the structure $(\mathbb{Q}, +, \cdot, 0, 1)$: the set of $\mathcal{L}_{\mathrm{ring}}$-sentences true in $\mathbb{Q}$. Fix an effective Gödel numbering of $\mathcal{L}_{\mathrm{ring}}$-sentences.

**Theorem (J. Robinson).** $\operatorname{Th}(\mathbb{Q})$ is undecidable: the set of Gödel numbers of sentences in $\operatorname{Th}(\mathbb{Q})$ is not computable.

Conventions: the language has no parameters and no further constants; quantifiers range over $\mathbb{Q}$; the result concerns the full first-order theory, with arbitrary alternations of quantifiers. Whether the existential fragment, which is Hilbert's tenth problem over $\mathbb{Q}$, is decidable is a different question that this statement does not address.

## Depends on

- [Complete theory of a first-order structure](../../../Logic/first-order-logic/theory-of-structure.md)

## Proof depends on

- [Robinson's definition of `ℤ` in `ℚ`](../../../Logic/model-theory/defining-the-integers-in-the-rationals/mem-range-int-cast-iff-robinson.md)
- [The first-order theory of the ring of integers is undecidable](../../../Logic/proof-theory/g-del-s-incompleteness-theorems/first-order-theory-of-the-integers-is-undecidable.md)

## Expansion

Robinson writes down a first-order formula $\psi(n)$ of $\mathcal{L}_{\mathrm{ring}}$ such that a rational number $n$ satisfies $\psi$ in $\mathbb{Q}$ exactly when $n \in \mathbb{Z}$. The formula quantifies over pairs $a, b$ of nonzero rationals and uses solvability of $2 + abk^2 + bz^2 = x^2 + ay^2$ as a predicate in $k$; the nontrivial direction uses the Hasse–Minkowski local-global principle for quadratic forms to show that, for suitable primes $p$ and $q$, this predicate forces $v_p(k) \ge 0$, and the inductive form of $\psi$ then forces $v_p(n) \ge 0$ for every prime $p$. Relativizing every quantifier of a sentence about $(\mathbb{Z}, +, \cdot, 0, 1)$ to $\psi$ gives a computable translation of the first-order theory of the ring of integers into $\operatorname{Th}(\mathbb{Q})$. The first-order theory of $(\mathbb{Z}, +, \cdot, 0, 1)$ is undecidable by the work of Gödel and Church, so $\operatorname{Th}(\mathbb{Q})$ is undecidable.

## Sources

- Julia Robinson, *Definability and decision problems in arithmetic*, J. Symbolic Logic 14 (1949), no. 2, 98–114, https://doi.org/10.2307/2266510; cited for attribution, with the statement and the formula as read in Jochen Koenigsmann's survey below (Theorem 2.11 and Corollary 2.12 of arXiv:1309.0441v1).
- Jochen Koenigsmann, *Undecidability in number theory*, in: Model Theory in Algebra, Analysis and Arithmetic, Lecture Notes in Mathematics 2111, Springer, 2014, pp. 159–195, https://doi.org/10.1007/978-3-642-54936-6_5; Robinson's definition is Theorem 2.11 and the undecidability of the theory of $\mathbb{Q}$ is Corollary 2.12 of arXiv:1309.0441v1.
