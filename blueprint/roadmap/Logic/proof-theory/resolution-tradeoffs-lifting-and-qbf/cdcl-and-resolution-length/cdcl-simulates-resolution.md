# CDCL with restarts polynomially simulates resolution

If a CNF formula in $n$ variables has a resolution refutation $\pi$, then it has a CDCL refutation of size $O(n^3 |\pi|)$, using nondeterministically chosen decisions, an asserting learning scheme, restarts and no clause deletion.

**Theorem.** Let $\phi$ be a CNF formula in $n$ variables and let $\pi$ be a resolution refutation of $\phi$. Then $\phi$ has a CDCL refutation of size $O(n^3 |\pi|)$. Consequently CDCL, viewed as a proof system, and resolution are polynomially equivalent: every CDCL refutation contains resolution derivations of its learned clauses, and conversely resolution refutations are transformed into CDCL refutations with polynomial overhead.

This improves the $O(n^4 |\pi|)$ bound of Pipatsrisawat and Darwiche, which holds for any reasonable learning scheme and restart policy but, like this result, relies on a decision strategy chosen with knowledge of $\pi$ and on never deleting learned clauses.

## Expansion

Process $\pi$ clause by clause. Call a derived clause $C$ **reliable** for the current clause database if no literal of $C$ is propagated by a trail whose decisions are the negations of the other literals of $C$ (a strengthening of the 1-empowering notion). If the next clause of $\pi$ is already unreliable, nothing is done. Otherwise one decides the negations of its literals; since it is reliable, these decisions do not block each other, unit propagation runs into a conflict (using the unreliability of its two premises), and the learned asserting clause makes progress. After $O(n^3)$ trail steps the clause becomes unreliable, and one restarts. The empty clause can never become unreliable, so at the latest when $\pi$ reaches $\bot$ the CDCL run learns $\bot$. The constructive variant of Atserias, Fichte and Thurley shows that random decisions suffice when $\phi$ has a refutation of small width.

## Depends on

- [Conflict-driven clause learning as a proof system](cdcl-proof-system.md)
- [Resolution refutation](../../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)

## Proof depends on

None.

## Sources

- O. Beyersdorff, B. Böhm, "Understanding the relative strength of QBF CDCL solvers and QBF resolution", *Logical Methods in Computer Science* 19(2:2), 2023 (conference version ITCS 2021), doi:10.46298/lmcs-19(2:2)2023, arXiv:2109.04862v5 (Theorem 7.2 and Definition 7.1, Section 7; the quantified version is the main theorem of Section 6).
- J. Nordström, "On the interplay between proof complexity and SAT solving", *ACM SIGLOG News* 2(3), 2015, doi:10.1145/2743014.2743018 (Section 3.1).
