# Nullstellensatz proof system

A Nullstellensatz refutation of polynomial equations $p_1 = \dots = p_m = 0$ over a field $\mathbb{F}$ and Boolean variables is one identity $\sum_i r_i p_i + \sum_j s_j (x_j^2 - x_j) = 1$; its degree is the largest degree of a product in it and its size counts the monomials of the products before any cancellation.

Let $\mathbb{F}$ be a field and $p_1, \dots, p_m \in \mathbb{F}[x_1, \dots, x_n]$. A **Nullstellensatz refutation** of $p_1, \dots, p_m$ over $\mathbb{F}$ is a tuple of polynomials $(r_1, \dots, r_m; s_1, \dots, s_n)$ in $\mathbb{F}[x_1, \dots, x_n]$ such that

$$
\sum_{i=1}^{m} r_i(\vec{x}) \, p_i(\vec{x}) + \sum_{j=1}^{n} s_j(\vec{x}) \, (x_j^2 - x_j) = 1 .
$$

Its **degree** is $\max\{\deg(r_i p_i), \deg(s_j (x_j^2 - x_j))\}$. For a polynomial $p$ let $\mathrm{mSize}(p)$ be the number of monomials of $p$ written as a linear combination of monomials; the **size** of the refutation is

$$
\sum_{i=1}^{m} \mathrm{mSize}(r_i) \, \mathrm{mSize}(p_i) + \sum_{j=1}^{n} 2 \, \mathrm{mSize}(s_j) ,
$$

the number of monomials encountered when every product is expanded, counted before cancellation. A refutation exists exactly when $p_1 = \dots = p_m = 0$ has no $0$-$1$ solution. A CNF formula is refuted through its clause polynomials: reading $1$ as true, the clause $\bigvee_{x \in P} x \vee \bigvee_{y \in N} \neg y$ is encoded as $\prod_{x \in P} (1 - x) \prod_{y \in N} y$.

**Multilinear variant.** A **multilinear Nullstellensatz refutation** of $p_1, \dots, p_m$ works in the quotient ring $\mathbb{F}[x_1, \dots, x_n]/(x_j^2 - x_j : j \in [n])$: it is an identity

$$
\sum_{i=1}^{m} r_i(\vec{x}) \, p_i(\vec{x}) = 1
$$

in which every product is replaced by its multilinearization, so the Boolean axioms are no longer needed. Degree and size are measured as above, with the products multilinearized; any refutation as above stays valid after multilinearization, so multilinear degree and size are never larger.

Other sources measure size differently, for example as the bit size of the encodings of the polynomials $r_i p_i$ and $s_j (x_j^2 - x_j)$; a statement that depends on the measure names it.

## Depends on

- [CNF formula](../../propositional-logic/conjunctive-normal-form/cnf.md)

## Proof depends on

None.

## Sources

- Susanna F. de Rezende, Jakob Nordström, Or Meir, Robert Robere, "Nullstellensatz size-degree trade-offs from reversible pebbling", *34th Computational Complexity Conference (CCC 2019)*, LIPIcs 137, 2019, https://doi.org/10.4230/LIPIcs.CCC.2019.18; numbering of arXiv:2001.02481v1 (Section 2.1, refutation (2.1), size measure (2.2), and the multilinear refutation (2.4)).
- Christoph Berkholz, "The relation between polynomial calculus, Sherali-Adams, and sum-of-squares proofs", *35th Symposium on Theoretical Aspects of Computer Science (STACS 2018)*, LIPIcs 96, 2018, https://doi.org/10.4230/LIPIcs.STACS.2018.11 (Section 2.1, identity (1) and its degree and size).
