# Order problem and torsion problem of a finitely generated group

The order problem of a finitely generated group asks for an algorithm that computes, from a word in the generators, the order of the element it represents; the torsion problem asks only whether that order is finite.

Let $G$ be a group, $X$ a finite set and $\pi\colon (X \cup X^{-1})^* \to G$ the canonical monoid homomorphism for a map $X \to G$ whose image generates $G$. The order of $g \in G$ is the least $n \ge 1$ with $g^n = 1$, or $\infty$ if there is none.

- The order problem is solvable for $G$ if some algorithm computes, given a word $w \in (X \cup X^{-1})^*$, the order of $\pi(w)$ (an element of $\{1, 2, 3, \dots\} \cup \{\infty\}$).
- The torsion problem (also called the order problem when posed as a decision problem) is solvable for $G$ if some algorithm decides, given $w$, whether $\pi(w)$ has finite order.

Solvability of either problem does not depend on the finite generating set.

## Depends on

- [Group](../../../group-basics/group.md)

## Proof depends on

- [Solvable word problem](../../word-problem-for-groups/word-problem-solvable.md)

## Expansion

If the order can be computed then the torsion problem and the word problem are solvable: $\pi(w) = 1$ exactly when its order is $1$. Conversely, if the torsion problem and the word problem are solvable, the order is computed by first deciding finiteness and then testing $\pi(w)^n = 1$ for $n = 1, 2, \dots$. So an unsolvable torsion problem makes the order problem unsolvable, and in a group with solvable word problem the two problems are equivalent.

## Sources

- J. McCool, "Unsolvable problems in groups with solvable word problem", Canadian Journal of Mathematics 22 (1970), no. 4, 836–838, https://doi.org/10.4153/CJM-1970-094-6 (Section 1, definition of the order problem). Read in the open-access copy https://www.cambridge.org/core/services/aop-cambridge-core/content/view/CFCCC6647CA6F09E49AC90B5F042502F/S0008414X00047544a.pdf/div-class-title-unsolvable-problems-in-groups-with-solvable-word-problem-div.pdf (the published version).
- J. Belk and C. Bleak, "Some undecidability results for asynchronous transducers and the Brin–Thompson group 2V", Transactions of the American Mathematical Society 369 (2017), no. 5, 3157–3172, https://doi.org/10.1090/tran/6963; arXiv:1405.0982v1 (Section 1 of arXiv:1405.0982v1, definition of the torsion problem).
- P. Gillibert, "An automaton group with undecidable order and Engel problems", Journal of Algebra 497 (2018), 363–392, https://doi.org/10.1016/j.jalgebra.2017.11.049; arXiv:1710.09733v2 (Section 2 of arXiv:1710.09733v2, the order problem as a decision problem and its relation to the word problem).
