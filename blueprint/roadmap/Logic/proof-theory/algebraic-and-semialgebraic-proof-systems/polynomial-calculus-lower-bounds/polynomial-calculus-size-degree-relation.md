# Size-degree relation for polynomial calculus

Every polynomial calculus resolution refutation of an unsatisfiable CNF formula of size $S$ over $n$ variables can be converted to one of degree $W + O(\sqrt{n \log S})$, $W$ the formula width; so when the minimum degree $D$ is at least $W$, size is $\exp(\Omega((D - W)^2/n))$.

Polynomial calculus (PC) and polynomial calculus resolution (PCR) are as on the linked definition page, with the following conventions of the source. Let $\mathbb{F}$ be any field and $F$ a CNF formula. A PCR refutation of $F$ over $\mathbb{F}$ is a sequence of polynomials $P_1, \dots, P_\tau$ in $\mathbb{F}[x, \bar{x}, y, \bar{y}, \dots]$, written as linear combinations of monomials, with $P_\tau = 1$, in which each line is a clause axiom $\prod_{x \in L^+} x \cdot \prod_{y \in L^-} \bar{y}$ encoding a clause of $F$, a Boolean axiom $x^2 - x$, a complementarity axiom $x + \bar{x} - 1$, or follows from earlier lines by a linear combination $\alpha Q + \beta R$ ($\alpha, \beta \in \mathbb{F}$) or a multiplication $x Q$ by a variable. Dropping complementarity axioms and writing negative literals as $1 - x$ gives polynomial calculus (PC). The size $S$ of a refutation is the number of monomials counted with repetition, its degree $\mathrm{Deg}$ the maximum degree of a monomial in it; the minimum degree is the same for PC and PCR.

**Theorem.** Let $F$ be an unsatisfiable CNF formula of width $W(F)$ over $n$ variables, and write $D = \mathrm{Deg}(F \vdash \bot)$ and $S = S_{\mathrm{PCR}}(F \vdash \bot)$. Then

$$
D \le W(F) + O\left( \sqrt{n \log S} \right) ,
$$

and consequently, whenever $D \ge W(F)$,

$$
S = \exp\left( \Omega\left( \frac{(D - W(F))^2}{n} \right) \right) .
$$

The guard $D \ge W(F)$ cannot be dropped: squaring loses the sign of $D - W(F)$. For example, the formula consisting of the clauses $x_1$, $\neg x_1$ and $x_1 \vee \dots \vee x_n$ has a PCR refutation of degree $1$ and constant size, while $(D - W(F))^2 / n = (n-1)^2/n$. The cited full version prints the squared bound without the guard; equivalently one may use $\max(0, D - W(F))^2/n$ in the exponent.

## Proof sketch

The relation was proved by Impagliazzo, Pudlák and Sgall for polynomial calculus, and the same proof works for PCR. The proof is a degree-reduction argument that converts a small refutation into one of low degree. Its counterpart for semialgebraic systems is the size-degree trade-off for Positivstellensatz and Sums-of-Squares proofs. Note that multilinear polynomial calculus refutes every unsatisfiable $k$-CNF in length linear in the formula size, so size, not length, is the meaningful measure.

## Depends on

- [CNF formula](../../../propositional-logic/conjunctive-normal-form/cnf.md)
- [Width of a CNF formula](../../../propositional-logic/resolution-size-and-width/max-clause-width.md)
- [Polynomial calculus](../polynomial-calculus.md)

## Proof depends on

None.

## Sources

- Mladen Mikša, Jakob Nordström, "A generalized method for proving polynomial calculus degree lower bounds", *30th Computational Complexity Conference (CCC 2015)*, LIPIcs 33, 2015, https://doi.org/10.4230/LIPIcs.CCC.2015.467; numbering of the full version, ECCC report TR15-078 (Definition 2.1, Theorem 2.2, which states the squared bound without the guard $D \ge W$, Proposition 2.3).
- Russell Impagliazzo, Pavel Pudlák, Jiří Sgall, "Lower bounds for the polynomial calculus and the Gröbner basis algorithm", *Computational Complexity* 8(2), 1999, https://doi.org/10.1007/s000370050024 (original source of the relation).
