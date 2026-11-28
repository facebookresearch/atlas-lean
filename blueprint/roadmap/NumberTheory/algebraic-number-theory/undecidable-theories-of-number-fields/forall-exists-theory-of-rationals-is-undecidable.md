# The universal-existential theory of the field of rational numbers is undecidable

No algorithm decides, for a first-order sentence of the language of rings consisting of a block of universal quantifiers followed by a block of existential quantifiers in front of a quantifier-free formula, whether it is true in the field $\mathbb{Q}$.

Work in the language of rings $\mathcal{L}_{\mathrm{ring}} = \{+, \cdot, 0, 1\}$ with equality and without parameters. A $\forall\exists$-sentence is a sentence of the form

$$
\forall x_1 \cdots \forall x_m \, \exists y_1 \cdots \exists y_k \; \theta(x_1, \dots, x_m, y_1, \dots, y_k)
$$

with $m, k \ge 0$ and $\theta$ quantifier-free. Let $\operatorname{Th}_{\forall\exists}(\mathbb{Q})$ be the set of $\forall\exists$-sentences true in $(\mathbb{Q}, +, \cdot, 0, 1)$, a subset of the complete theory $\operatorname{Th}(\mathbb{Q})$.

**Theorem.** $\operatorname{Th}_{\forall\exists}(\mathbb{Q})$ is undecidable: under an effective Gödel numbering, the set of Gödel numbers of its members is not computable.

Equivalently, by negation, the set of true $\exists\forall$-sentences is not computable. The existential fragment, Hilbert's tenth problem over $\mathbb{Q}$, is a different question that this statement does not settle.

## Depends on

- [Complete theory of a first-order structure](../../../Logic/first-order-logic/theory-of-structure.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Koenigsmann: `ℚ ∖ ℤ` is Diophantine over `ℚ`](../../../Logic/model-theory/defining-the-integers-in-the-rationals/not-mem-range-int-cast-iff-exists-eval-e.md)
- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)
- [The halting problem is recognizable by multi-stack machines](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/tm2-recognizable-halting.md)
- [The halting problem is undecidable by multi-stack machines](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halting.md)

## Expansion

Koenigsmann's universal definition of $\mathbb{Z}$ in $\mathbb{Q}$ gives a polynomial $g(t; x_1, \dots, x_N)$ with integer coefficients such that a rational $t$ is an integer exactly when $g(t; \bar x) \neq 0$ for all $\bar x \in \mathbb{Q}^N$. For $f \in \mathbb{Z}[t_1, \dots, t_n]$, the polynomial $f$ has an integer zero exactly when

$$
\exists t_1 \cdots \exists t_n \, \forall \bar x^{(1)} \cdots \forall \bar x^{(n)} \; \Bigl( f(t_1, \dots, t_n) = 0 \wedge \bigwedge_{i=1}^{n} g(t_i; \bar x^{(i)}) \neq 0 \Bigr)
$$

holds in $\mathbb{Q}$, an $\exists\forall$-sentence computable from $f$, where the integer coefficients are written as sums of $1$ and their negatives moved across the equation. Hilbert's tenth problem over $\mathbb{Z}$ is undecidable by the Davis–Putnam–Robinson–Matiyasevich theorem applied to a listable undecidable set such as the halting set, so the true $\exists\forall$-sentences, and with them by negation the true $\forall\exists$-sentences, form an undecidable set.

## Sources

- Jochen Koenigsmann, *Undecidability in number theory*, in: Model Theory in Algebra, Analysis and Arithmetic, Lecture Notes in Mathematics 2111, Springer, 2014, pp. 159–195, https://doi.org/10.1007/978-3-642-54936-6_5; the universal definition is Theorem 4.1 and the undecidability of $\operatorname{Th}_{\forall\exists}(\mathbb{Q})$ is Corollary 4.4 of arXiv:1309.0441v1.
- Jochen Koenigsmann, *Defining $\mathbb{Z}$ in $\mathbb{Q}$*, Ann. of Math. (2) 183 (2016), no. 1, 73–93, https://doi.org/10.4007/annals.2016.183.1.2, for the universal definition of $\mathbb{Z}$ in $\mathbb{Q}$, as read in Theorem 4.1 of arXiv:1309.0441v1.
