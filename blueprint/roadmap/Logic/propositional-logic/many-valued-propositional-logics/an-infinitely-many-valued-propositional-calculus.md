# An infinitely many-valued propositional calculus with undecidable validity

There is a propositional calculus, with infinitely many truth values and finitely many connectives, whose set of valid formulas is not recursive: Nakamura builds one whose valid formulas encode first-order validity.

**The calculus $L$.** Truth values are the functions $g:\mathbb N^3\to\{0,1\}^{\mathbb N}$, assigning to each coordinate $(x,y,z)$ an infinite $0$–$1$ sequence. The *designated value* has every entry of every sequence equal to $1$. The connectives are:

- negation $\neg$ and disjunction $\vee$, acting entrywise;
- monadic operators $X$, $Y$, $Z$, which copy the sequence at the diagonal point $(i,i,i)$ to every coordinate whose $x$-, $y$- or $z$-coordinate, respectively, is $i$;
- quantifier-like operators $\exists_x$, $\exists_y$, $\exists_z$, where $\exists_x g$ has entry $1$ at position $\lambda$ of $(x,j,k)$ for every $x$ exactly when some $a$ gives $g(a,j,k)$ entry $1$ at position $\lambda$, and similarly for $y$ and $z$;
- an operator $O$ that turns each sequence into the constant sequence $1$ if it has some entry $1$, and into the constant sequence $0$ otherwise.

A formula built from propositional variables with these connectives is *valid* if it takes the designated value under every assignment of truth values to its variables.

**Theorem (Nakamura).** The validity problem of $L$ is recursively unsolvable.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Validity of first-order sentences is undecidable](../../../TheoryOfComputation/undecidable-problems/validity-of-first-order-sentences-is-undecidable.md)
- [Downward Löwenheim–Skolem theorem](../../model-theory/downward-lowenheim-skolem-theorem.md)

## Expansion

By Surányi's reduction theorem, every first-order formula can be effectively transformed into one of the form $\forall x\,\exists y\,\exists z\,M_1\vee\exists x\,\exists y\,\forall z\,M_2$ with $M_1$, $M_2$ quantifier-free and containing only unary and binary predicates, equivalent with respect to universal validity. A translation $h$ maps such a formula to a formula of $L$, sending unary and binary predicates to formulas built with $O$ and the copying operators and first-order quantifiers to the operators $\exists_x$, $\exists_y$, $\exists_z$. Using the downward Löwenheim–Skolem theorem, linked above, to restrict to countable domains, whose elements are placed on the diagonal of $\mathbb N^3$, one shows that the reduction form is universally valid exactly when its translation is valid in $L$. A good expansion links a page for Surányi's reduction theorem (the Theorem of §2 of the source).

## Sources

- A. Nakamura, "On a propositional calculus whose decision problem is recursively unsolvable", *Nagoya Mathematical Journal* 38, pp. 145–152, 1970, doi:[10.1017/S0027763000013593](https://doi.org/10.1017/S0027763000013593), the copy read: the system $L$ and its truth-value functions in §1, the reduction theorem, the translation and Theorems 1 and 2 in §2, and their proofs in §3.
