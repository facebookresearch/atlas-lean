# Presburger arithmetic with the generalized polynomial ⌊βn⌊αn⌉⌉ is undecidable

Adding to Presburger arithmetic over the integers the function n ↦ ⌊βn⌊αn⌉⌉, built with the nearest-integer operation, yields an undecidable first-order theory whenever 1, α, α² are linearly independent over the rationals and β is nonzero.

**Setting.** For a real number $x$ let $\lfloor x\rceil=\lfloor x+1/2\rfloor$ be the nearest integer to $x$. *Generalized polynomials* are the functions $\mathbb Z\to\mathbb R$ built from real polynomials using the integer part function, addition and multiplication. For $\alpha,\beta\in\mathbb R$ consider

$$
g(n)=\bigl\lfloor\beta n\lfloor\alpha n\rceil\bigr\rceil\qquad(n\in\mathbb Z),
$$

and the first-order theories $\mathrm{Th}(\mathbb Z;<,+,g)$ and $\mathrm{Th}(\mathbb Z;+,1,g)$, with $g$ a unary function symbol.

**Theorem (Konieczny).** Let $\alpha,\beta\in\mathbb R$ with $\beta\neq0$ be such that $1,\alpha,\alpha^2$ are linearly independent over $\mathbb Q$. Then the first-order theory of $(\mathbb Z;<,+,g)$ is undecidable (Theorem A of the source), and so is the first-order theory of $(\mathbb Z;+,1,g)$ (Corollary 1.2).

For an ordinary polynomial $f$ of degree at least $2$, multiplication is definable in $(\mathbb Z;+,f)$, so undecidability is immediate; for generalized polynomials no such definition is available, and the source conjectures that $\mathrm{Th}(\mathbb Z;<,+,g)$ is undecidable for every generalized polynomial $g$ with $\liminf_{n\to\infty}|g(n)|/n^2>0$. The theorem verifies this for one family. The source also proves undecidability of $\mathrm{Th}(\mathbb Z;<,+,g)$ for a bounded generalized polynomial, the quadratic Sturmian-type sequence $g(n)=1$ if the fractional part of $\alpha n^2$ is less than $\rho$ and $g(n)=0$ otherwise, whenever $0<\rho<1/4$ and $\alpha$ is not a rational linear combination of $1$ and $\rho$ (Theorem B).

## Depends on

- [Complete theory of a first-order structure](../../../first-order-logic/theory-of-structure.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The core is a "poor man's multiplication" lemma: if $Q\subseteq\mathbb Z^4$ contains only tuples of the form $(m,km,lm,klm)$ and, for every finite $F\subseteq\mathbb Z^2$, some $m\neq0$ with $(m,km,lm,klm)\in Q$ for all $(k,l)\in F$, then $\mathrm{Th}(\mathbb Z;+,1,Q)$ is undecidable, because the partial operations $a\times_m b=c\iff(m,a,b,c)\in Q$ behave like multiplication on any finite set, which suffices to interpret arithmetic on finite initial segments and hence to encode undecidable problems. The main work is to define such a set $Q$ in $(\mathbb Z;<,+,g)$, which is where the linear independence of $1,\alpha,\alpha^2$ is used. For the version without order, the relation $<$ is definable in $(\mathbb Z;+,1,g)$ through a result essentially due to Neale that every sufficiently large integer is a sum of a bounded number of values $n\lfloor\alpha n\rceil$. A good expansion links pages for the poor man's multiplication lemma and for the definability of order.

## Sources

- J. Konieczny, "Decidability of extensions of Presburger arithmetic by generalised polynomials", *Logical Methods in Computer Science* 21(4), paper 1, 2025, doi:[10.46298/lmcs-21(4:1)2025](https://doi.org/10.46298/lmcs-21(4:1)2025); read in arXiv:2402.09647v4 ([arXiv](https://arxiv.org/abs/2402.09647v4)): Theorems A and B and Corollary 1.2 in the introduction, the conjecture before them, and Proposition 2.1 (poor man's multiplication) opening Section 2.
