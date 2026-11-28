# UNFO with inequalities or negated atoms is a conservative reduction class

Allowing inequalities, or negated relational atoms, in the unary negation fragment of first-order logic produces a conservative reduction class, so satisfiability and finite satisfiability become undecidable.

**Theorem (ten Cate and Segoufin).** The extensions $\mathrm{UNFO}^{\neq}$ and $\mathrm{UNFO}^{\neg}$ of the [unary negation fragment](unary-negation-fragment-and-fixpoint-logic.md) are conservative reduction classes of first-order logic. Hence satisfiability is undecidable for each of them, both over arbitrary structures and over finite structures.

UNFO itself has the finite model property and a 2ExpTime-complete satisfiability problem. Unary negation alone keeps the logic decidable, and adding inequalities, or negated relational atoms, already loses this.

## Depends on

- [Unary negation fragment and unary negation fixpoint logic](unary-negation-fragment-and-fixpoint-logic.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Sentences with one universal quantifier and two unary functions or one binary function are undecidable](../undecidable-prefix-classes/one-universal-quantifier-with-function-symbols.md)

## Expansion

The proof starts from the conservative reduction class of one-variable first-order logic with two unary functions and equality, the class $[\forall, (0), (2)]_=$. Represent the functions by binary relations $F$ and $G$. In $\mathrm{UNFO}^{\neq}$, the sentence $\neg\exists x y z\,(F(x,y) \wedge F(x,z) \wedge y \neq z)$ says that $F$ is the graph of a partial function, and similarly for $G$, while $f(x) = g(x)$ becomes $\exists y z\,(F(x,y) \wedge G(x,z) \wedge y = z)$. In $\mathrm{UNFO}^{\neg}$, negated atoms let a binary relation $E$ be forced to be an equivalence relation, which then plays the role of equality, and $F$ and $G$ are forced to be functions on $E$-classes. The proof uses that $[\forall, (0), (2)]_=$ is a conservative reduction class (cited in the proof of Theorem 7.1 of the source), which is stronger than the undecidability of its satisfiability problem and is stated on the linked page.

## Sources

- B. ten Cate and L. Segoufin, "Unary negation", *Logical Methods in Computer Science* 9(3), paper 25, 2013, doi:[10.2168/LMCS-9(3:25)2013](https://doi.org/10.2168/LMCS-9(3:25)2013). Numbering of the version read, arXiv:1309.2069v2: Theorem 7.1 and its proof in Section 7.3, and Section 1 (decidability of UNFO).
