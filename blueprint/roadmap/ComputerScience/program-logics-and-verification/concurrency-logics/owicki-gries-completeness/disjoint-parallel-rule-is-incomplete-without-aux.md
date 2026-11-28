# Hoare's disjoint-parallelism rule is incomplete without auxiliary variables

Even for parallel programs whose components share no changed variables, Hoare's rules with the disjoint-parallelism rule cannot derive the valid triple $\{x = y\}\,[x := x + 1 \parallel y := y + 1]\,\{x = y\}$; an auxiliary variable recording the common initial value yields a derivation.

A *disjoint parallel program* $[S_1 \parallel \dots \parallel S_n]$, $n \ge 2$, has while-program components with $\mathrm{change}(S_i) \cap \mathrm{var}(S_j) = \emptyset$ for all $i \ne j$, where $\mathrm{var}(S)$ is the set of variables occurring in $S$ and $\mathrm{change}(S)$ the set of variables on the left of an assignment in $S$; its semantics is interleaving. Let $\mathrm{PW}$ be the proof system for while programs (skip, assignment, sequencing, conditional, loop and consequence, the implications of consequence being formulas of a first-order language of integer arithmetic true in the standard structure of the integers, over which program variables range). The *disjoint-parallelism rule* PDJ is: from $\{p_i\}\,S_i\,\{q_i\}$ for $i = 1, \dots, n$ infer

$$\Big\{\bigwedge_{i=1}^{n} p_i\Big\}\,[S_1 \parallel \dots \parallel S_n]\,\Big\{\bigwedge_{i=1}^{n} q_i\Big\},$$

provided $\mathrm{free}(p_i, q_i) \cap \mathrm{change}(S_j) = \emptyset$ for all $i \ne j$.

**Theorem.** The triple $\{x = y\}\,[x := x + 1 \parallel y := y + 1]\,\{x = y\}$ is valid in the sense of partial correctness but not derivable in $\mathrm{PW}$ + PDJ.

With the [auxiliary-variable rule](owicki-gries-system-with-auxiliary-variables.md) it is derivable: for a fresh $z$, PDJ gives $\{x = z \wedge y = z\}\,[x := x + 1 \parallel y := y + 1]\,\{x = z + 1 \wedge y = z + 1\}$, the assignment $z := x$ establishes $x = z \wedge y = z$ from $x = y$, consequence weakens the postcondition to $x = y$, and $z$, auxiliary and absent from the postcondition, is deleted.

## Depends on

- [Owicki–Gries proof system with auxiliary variables](owicki-gries-system-with-auxiliary-variables.md)

## Proof depends on

- [Owicki–Gries proof system with auxiliary variables](owicki-gries-system-with-auxiliary-variables.md)

## Expansion

The source's proof: a derivation must apply PDJ to proofs of $\{p_1\}\,x := x + 1\,\{q_1\}$ and $\{p_2\}\,y := y + 1\,\{q_2\}$ and then consequence, so $x = y \to p_1 \wedge p_2$ and $q_1 \wedge q_2 \to x = y$ are valid. From $p_1 \to q_1[x := x + 1]$ and the validity of $p_1[x := y]$ it follows that $q_1[x := y + 1]$ is valid, and the source then instantiates $y$ to $x - 1$ to conclude that $q_1$ is valid; likewise $q_2$, contradicting $q_1 \wedge q_2 \to x = y$. The source states no interpretation explicitly; this argument uses the substitution of $x - 1$ and that $x = y$ is not valid, which the integer interpretation fixed above provides. A development needs the syntax of disjoint parallel programs and the side conditions of PDJ.

## Sources

- S. de Gouw and J. Rot, "Effectively eliminating auxiliaries", in *Theory and Practice of Formal Methods: Essays Dedicated to Frank de Boer on the Occasion of His 60th Birthday*, LNCS 9660, Springer, 2016, pp. 226–241, <https://doi.org/10.1007/978-3-319-30734-3_16>, author copy <http://jurriaan.creativecode.org/wp-content/uploads/2013/04/ghost.pdf>: Section 2 (notation $\mathrm{var}$, $\mathrm{change}$, $\mathrm{free}$), Section 3 (Figure 3, proof system PW) and Section 5 (disjoint parallel programs, Rule PDJ, Theorem 3 and its proof, Example 2). Numbering follows the author copy; the source attributes the result to Exercise 7.9 of Apt, de Boer and Olderog's textbook.
- K. R. Apt and E.-R. Olderog, "Fifty years of Hoare's logic", *Formal Aspects of Computing* 31(6):751–807, 2019, <https://doi.org/10.1007/s00165-019-00501-3>, author version arXiv:1904.03917v1, <https://arxiv.org/abs/1904.03917v1>: Section 8.1 (the same triple is not provable with the DISJOINT PARALLELISM rule and the rules of the system for while programs).
