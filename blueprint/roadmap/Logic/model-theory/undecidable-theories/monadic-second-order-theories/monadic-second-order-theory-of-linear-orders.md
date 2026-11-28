# Monadic second-order theory of linear orders

The monadic theory of a linear order, or of a class of linear orders, is the set of sentences of monadic second-order logic, first-order logic over the order with added variables and quantifiers ranging over subsets, that are true in it.

**Monadic logic.** For a signature with the binary symbol $<$ (and possibly unary predicates), monadic second-order formulas are built from atomic formulas $x < y$, $x = y$ and $x \in X$, with $x, y$ individual variables and $X$ a set variable, using Boolean connectives, quantifiers $\exists x, \forall x$ over elements and quantifiers $\exists X, \forall X$ over subsets of the domain. In the *weak* monadic logic set quantifiers range over finite sets only; other variants restrict them to countable, closed or Borel sets.

**Monadic theories.** For a class $K$ of linear orders, the *monadic theory* of $K$ is the set of monadic sentences true in every member of $K$. The *monadic theory of order* is the monadic theory of the class of all linear orders, and the *monadic theory of the real order* is the set of monadic sentences true in $(\mathbb{R}, <)$. Such a theory is *decidable* if membership of a given sentence is decidable.

## Depends on

- [Partially ordered set](../../../../Order/ordered-sets/partial-order.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

With pairing functions available, monadic logic is essentially full second-order logic, which is why the order-only setting matters. The monadic theory of $(\omega, <)$ is decidable (Büchi), as are those of the countable ordinals, of $\omega_1$, and of the class of countable linear orders (Rabin), and the weak monadic theory of order (Läuchli). The real line is the first natural case where decidability fails.

## Sources

- S. Shelah, "The monadic theory of order", *Annals of Mathematics* (2) 102(3):379–419, 1975, doi:10.2307/1971037; read as the slightly corrected version arXiv:2305.00968v1, <https://arxiv.org/abs/2305.00968v1>: Section 0 (definition of monadic logic and monadic theories, and the history of decidability results).
