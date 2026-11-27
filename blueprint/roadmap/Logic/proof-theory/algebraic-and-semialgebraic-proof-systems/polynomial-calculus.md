# Polynomial calculus

Polynomial calculus (PC) refutes polynomial equations over a field $\mathbb{F}$ and Boolean variables by deriving $1$ line by line, using linear combinations and multiplication by a variable; polynomial calculus resolution (PCR) adds a twin variable for each negated literal. Degree and monomial size are its main measures.

Let $\mathbb{F}$ be a field and $f_1, \dots, f_m \in \mathbb{F}[x_1, \dots, x_n]$. A **polynomial calculus derivation** of $g$ from $f_1, \dots, f_m$ over $\mathbb{F}$ is a sequence of polynomials $P_1, \dots, P_\tau$ with $P_\tau = g$, each written out as a linear combination of monomials, in which every line $P_i$ is

- an axiom $f_k$, or a Boolean axiom $x_j^2 - x_j$;
- a linear combination $\alpha Q + \beta R$ of earlier lines $Q, R$, with $\alpha, \beta \in \mathbb{F}$;
- a product $x_j Q$ of an earlier line $Q$ with a variable $x_j$.

A **PC refutation** of $f_1, \dots, f_m$ is a derivation of $1$; one exists exactly when $f_1 = \dots = f_m = 0$ has no $0$-$1$ solution. The **degree** of a derivation is the largest degree of a monomial in it, its **size** is the number of monomials in it counted with repetitions, and its **length** is the number $\tau$ of lines.

**Polynomial calculus resolution (PCR)** works in $\mathbb{F}[x_1, \bar{x}_1, \dots, x_n, \bar{x}_n]$, where each twin $\bar{x}_j$ is a separate formal variable, and adds the axioms $\bar{x}_j^2 - \bar{x}_j$ and the complementarity axioms $x_j + \bar{x}_j - 1$. Replacing every $\bar{x}_j$ by $1 - x_j$ turns a PCR refutation into a PC refutation of the same degree, so the minimum refutation degree is the same in both systems.

**CNF formulas.** A CNF formula is refuted through the encodings of its clauses. Reading $1$ as true, the clause $\bigvee_{x \in P} x \vee \bigvee_{y \in N} \neg y$ becomes the polynomial $\prod_{x \in P} (1 - x) \prod_{y \in N} y$ in PC and $\prod_{x \in P} \bar{x} \prod_{y \in N} y$ in PCR; a $0$-$1$ assignment makes it vanish exactly when the assignment satisfies the clause. Reading $0$ as true instead swaps the roles of $x$ and $\bar{x}$ and changes neither degree nor size.

**Multilinear variant.** Some sources apply the Boolean axioms implicitly: lines are multilinear polynomials, the product $x_j Q$ is replaced by its multilinearization, and the degree of an inference is the largest degree of its premises, plus one for a multiplication. This never increases degree or size.

A statement about polynomial calculus that names no field holds over every field.

## Depends on

- [CNF formula](../../propositional-logic/conjunctive-normal-form/cnf.md)

## Proof depends on

None.

## Sources

- Mladen Mikša, Jakob Nordström, "A generalized method for proving polynomial calculus degree lower bounds", *30th Computational Complexity Conference (CCC 2015)*, LIPIcs 33, 2015, https://doi.org/10.4230/LIPIcs.CCC.2015.467; numbering of the full version, ECCC report TR15-078 (Definition 2.1 and the remarks after it).
- Michael Alekhnovich, Alexander A. Razborov, "Lower bounds for polynomial calculus: non-binomial case", *42nd IEEE Symposium on Foundations of Computer Science (FOCS 2001)*, 2001, https://doi.org/10.1109/SFCS.2001.959893; numbering of the authors' full version dated September 27, 2000 (Definition 2.1, multilinear polynomial calculus and the degree of an inference).
- Christoph Berkholz, "The relation between polynomial calculus, Sherali-Adams, and sum-of-squares proofs", *35th Symposium on Theoretical Aspects of Computer Science (STACS 2018)*, LIPIcs 96, 2018, https://doi.org/10.4230/LIPIcs.STACS.2018.11 (Sections 2.1 and 2.3, rules (2) and twin variables).
