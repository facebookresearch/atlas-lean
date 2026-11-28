# The first-order theory of the ring of integers is undecidable

The set of first-order sentences in the language of rings that are true in the ring $\mathbb{Z}$ of integers is not computable: no algorithm decides, for a sentence built from $+$, $\cdot$, $0$, $1$, equality, connectives and quantifiers over $\mathbb{Z}$, whether it holds in $\mathbb{Z}$.

Let $\mathcal{L}_{\mathrm{ring}} = \{+, \cdot, 0, 1\}$ be the language of rings, with equality, and let $\operatorname{Th}(\mathbb{Z})$ be the complete theory of the structure $(\mathbb{Z}, +, \cdot, 0, 1)$: the set of $\mathcal{L}_{\mathrm{ring}}$-sentences true in $\mathbb{Z}$. Fix an effective Gödel numbering of $\mathcal{L}_{\mathrm{ring}}$-sentences.

**Theorem.** $\operatorname{Th}(\mathbb{Z})$ is undecidable: the set of Gödel numbers of sentences in $\operatorname{Th}(\mathbb{Z})$ is not computable.

Conventions: the language has no parameters and no further constants; quantifiers range over $\mathbb{Z}$; the result concerns the full first-order theory, with arbitrary alternations of quantifiers.

## Depends on

- [Complete theory of a first-order structure](../../first-order-logic/theory-of-structure.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Tarski's undefinability theorem](tarski-s-undefinability-theorem.md)
- [Lagrange's four-square theorem](../../../NumberTheory/quadratic-forms-sums-of-squares/sums-of-squares/lagrange-four-square-theorem.md)

## Expansion

The proof has two steps. First, the theory $\operatorname{Th}(\mathbb{N})$ of $(\mathbb{N}, +, \cdot, 0, 1)$ is undecidable (Gödel): every computable function $f : \mathbb{N} \to \mathbb{N}$ has a defining formula $\varphi(v_0, v_1)$, with $f(n) = m$ exactly when $\varphi(n, m)$ holds in $\mathbb{N}$, so a decision procedure for $\operatorname{Th}(\mathbb{N})$ would make truth in $\mathbb{N}$ arithmetically definable, which the diagonal argument behind Tarski's undefinability theorem rules out. Second, by Lagrange's theorem the natural numbers are exactly the integers that are sums of four squares, so relativizing every quantifier of a sentence about $\mathbb{N}$ to $\exists a\, \exists b\, \exists c\, \exists d\; x = a^2 + b^2 + c^2 + d^2$ gives a computable translation of $\operatorname{Th}(\mathbb{N})$ into $\operatorname{Th}(\mathbb{Z})$. A good expansion adds and links pages for the arithmetical definability of computable functions and for the undecidability of $\operatorname{Th}(\mathbb{N})$.

## Sources

- Jochen Koenigsmann, *Undecidability in number theory*, in: Model Theory in Algebra, Analysis and Arithmetic, Lecture Notes in Mathematics 2111, Springer, 2014, pp. 159–195, https://doi.org/10.1007/978-3-642-54936-6_5; the undecidability of $\operatorname{Th}(\mathbb{N})$ is Theorem 1.1 with the proof sketch in Section 1.3, and the undecidability of $\operatorname{Th}(\mathbb{Z})$ is Corollary 1.3 of arXiv:1309.0441v1, the version read.
