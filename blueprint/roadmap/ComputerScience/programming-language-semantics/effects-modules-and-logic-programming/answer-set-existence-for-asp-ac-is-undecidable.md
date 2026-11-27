# Answer-set existence for ASP with algebraic constraints is undecidable

For non-ground answer set programs extended with algebraic constraints over semirings (ASP(AC)), both the existence of an answer set (equilibrium model) and strong equivalence of two programs are undecidable, even for safe programs over efficiently encoded semirings. Ground programs keep the complexity of disjunctive logic programs.

**Setting (Eiter and Kiesel).** An ASP(AC) program over a semiring signature for semirings $\mathcal{R}_1, \dots, \mathcal{R}_n$ is a finite set of rules

$$
\phi \leftarrow \psi_1, \dots, \psi_k, \neg\theta_1, \dots, \neg\theta_m,
$$

where each $\phi, \psi_i, \theta_j$ is an atom or an *algebraic constraint* $c \sim_{\mathcal{R}} \alpha$ or $x \sim_{\mathcal{R}} \alpha$ (with $\sim$ a comparison such as $=, <, \ge$ in an ordered semiring $\mathcal{R} = \mathcal{R}_i$, $c$ an element of $\mathcal{R}$ or $x$ a variable ranging over it) and $\alpha$ a quantifier-free *weighted formula* over $\mathcal{R}$, built from semiring values, variables and ordinary formulas (worth $1$ when true and $0$ when false) with $\oplus$, $\otimes$ and implication. Variables occurring only inside weighted formulas are summed over ($\oplus$-quantified); the others are universally quantified over the rule. The semantics is that of first-order weighted here-and-there logic, and the answer sets of a program are its equilibrium models: interpretations $\mathcal{I}$ with $(\mathcal{I}, \mathcal{I}) \models \Pi$ and $(\mathcal{I}', \mathcal{I}) \not\models \Pi$ for every $\mathcal{I}' \subsetneq \mathcal{I}$. A program is *safe* if every weighted formula is syntactically domain independent with respect to its summed variables and every global variable of a rule occurs in a positive body atom or is defined by a body constraint $X =_{\mathcal{R}} \beta$ in which $X$ occurs in no other body weighted formula. A semiring is *efficiently encoded* if it has an injective, polynomial-time computable encoding $e$ into $\mathbb{N}$ such that, for a constant $c$ and with $\lVert r \rVert = \log_2 e(r)$, one has $\lVert r_1 \odot r_2 \rVert \le \lVert r_1 \rVert + \lVert r_2 \rVert + c$ for $\odot \in \{\oplus, \otimes\}$ and $\max(\lVert -r \rVert, \lVert r^{-1} \rVert) \le \lVert r \rVert + c$, the encoded operations are computable in polynomial time, and the order is decidable in polynomial time; $\mathbb{B}$, $\mathbb{N}$, $\mathbb{Z}$, $\mathbb{Q}$ and the max-plus semiring qualify. Programs $\Pi_1, \Pi_2$ are *strongly equivalent* if $\Pi_1 \cup \Pi'$ and $\Pi_2 \cup \Pi'$ have the same equilibrium models for every program $\Pi'$.

**Theorem (Eiter and Kiesel).** For safe ASP(AC) programs over efficiently encoded semirings, the following problems are undecidable:

1. (SAT) given a program $\Pi$, does $\Pi$ have an equilibrium model?
2. (SE) given programs $\Pi_1$ and $\Pi_2$, are they strongly equivalent?

The paper also proves model checking for these programs to be in EXPTIME, and notes that SAT and SE remain undecidable for programs whose algebraic constraints are over the natural numbers. For safe programs without value invention whose head constraints are domain restricted and whose semirings are computable, SAT and SE are decidable (Theorem 25).

## Depends on

- [Semirings and formal power series on a free monoid](../../../TheoryOfComputation/regular-languages/automata-and-expressions/weighted-automata-and-rational-series/semirings-and-formal-power-series.md)

## Proof depends on

None.

## Expansion

The proof reduces from the mortal matrix problem: whether some product of matrices from a finite set $X = \{X_1, \dots, X_n\} \subseteq \mathbb{Z}^{d \times d}$ is the zero matrix. Over the efficiently encodable semiring $(\mathbb{Z}^{d \times d}, +, \cdot, 0_d, 1_d)$ the program with facts $p(X_i)$, the constraint $\bot \leftarrow \neg p(0_d)$ and the rule $p(Y) \leftarrow p(Z_1), p(Z_2), Y =_{\mathbb{Z}^{d \times d}} Z_1 \otimes Z_2$ has an equilibrium model exactly when $p(0_d)$ is derivable, that is, when $X$ is mortal. Dropping the constraint gives a negation-free program $\Pi'$ with $\Pi \equiv_s \Pi'$ if and only if $X$ is mortal, which gives SE.

## Sources

- Thomas Eiter and Rafael Kiesel, "ASP(AC): Answer Set Programming with Algebraic Constraints", Theory and Practice of Logic Programming 20(6), pp. 895–910, 2020, <https://doi.org/10.1017/S1471068420000393>; Theorem 23 (main statement), Definitions 2, 4, 7, 10, 12, 17, 19 and 21, and the remarks after Theorem 23 of arXiv:2008.04008v1, <https://arxiv.org/abs/2008.04008v1>.
- Michael S. Paterson, "Unsolvability in 3 × 3 Matrices", Studies in Applied Mathematics 49(1), pp. 105–107, 1970, <https://doi.org/10.1002/sapm1970491105>; undecidability of the mortal matrix problem, the source problem of the reduction; not read, the clause rests on the proof of Theorem 23 of the version read of the first source above, which states it.
- Julien Cassaigne, Vesa Halava, Tero Harju and François Nicolas, "Tighter Undecidability Bounds for Matrix Mortality, Zero-in-the-Corner Problems, and More", arXiv:1404.1442, <https://arxiv.org/abs/1404.1442>; the reference for matrix mortality that the paper above cites, not read.
