# Two-variable logic and its counting extension

Two-variable logic FO² is the set of first-order formulas, with equality, that use only the two variables $x$ and $y$ (reused as often as needed); its counting extension C² adds the quantifiers $\exists^{\leq k}$, $\exists^{\geq k}$ and $\exists^{=k}$ for every $k \in \mathbb{N}$.

**Formulas.** Over a relational signature with unary and binary predicate symbols (and no constants or function symbols), FO² formulas are the first-order formulas with equality whose variables, free or bound, are among $x, y$. C² formulas may in addition use the counting quantifiers $\exists^{\bowtie k} y\, \varphi$ for $\bowtie\, \in \{\leq, =, \geq\}$ and $k \in \mathbb{N}$, meaning that the number of $y$ satisfying $\varphi$ is $\bowtie k$.

**Distinguished symbols.** For a set $I$ of binary symbols, a logic such as $\mathrm{FO}^2(I)$ or $\mathrm{C}^2(I)$ is interpreted only over structures in which each symbol of $I$ has a prescribed meaning: a *linear order* $<_i$ or $\leq_i$, the *successor* of a linear order, or a *total preorder* $\precsim_i$ (a reflexive, transitive and total relation, that is, an equivalence relation whose classes are linearly ordered). The other symbols, unary or binary, are interpreted arbitrarily; notations such as $\mathrm{C}^2(*, 2, I)$ bound the number of unary (here unbounded) and additional binary symbols (here two) allowed besides $I$.

**Satisfiability.** A sentence is *finitely satisfiable* if it has a finite model of the prescribed kind. Without distinguished symbols, satisfiability and finite satisfiability are decidable and NEXPTIME-complete for FO² (Grädel, Kolaitis and Vardi) and for C² (Pratt-Hartmann).

## Depends on

- [Partially ordered set](../../../../Order/ordered-sets/partial-order.md)

## Proof depends on

None.

## Expansion

FO² cannot express transitivity, so orders and equivalences have to be imposed semantically to study them; for FO², finite satisfiability is undecidable with two linear orders together with their successors, with two total preorders, or with three equivalence relations, but decidable with two linear orders alone, with one linear order and one total preorder, or with two equivalence relations. C² can say that a binary symbol is the successor of a given linear order, using $\exists^{=1}$.

## Sources

- W. Charatonik and P. Witkowski, "Two-variable logic with counting and a linear order", *Logical Methods in Computer Science* 12(2), Paper 8, 2016, doi:10.2168/LMCS-12(2:8)2016; read as arXiv:1604.06038v2, <https://arxiv.org/abs/1604.06038v2>: Sections 1 and 2 (the logics $\mathrm{C}^2(\#_u, \#_b, I)$ and their known decidability) and Lemma 3.1 (successor definable in C²).
- T. Schwentick and T. Zeume, "Two-variable logic with two order relations", *Logical Methods in Computer Science* 8(1), Paper 15, 2012, doi:10.2168/LMCS-8(1:15)2012; read as arXiv:1110.1439v3, <https://arxiv.org/abs/1110.1439v3>: Sections 1 and 2 (two-variable logic over finite structures with linear orders and total preorders).
