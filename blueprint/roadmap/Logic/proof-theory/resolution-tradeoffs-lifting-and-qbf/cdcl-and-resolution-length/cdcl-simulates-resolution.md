# CDCL with restarts polynomially simulates resolution

If a CNF formula in $n$ variables has a resolution refutation $\pi$, then it has a CDCL refutation of size $O(n^3 |\pi|)$, using nondeterministically chosen decisions, an asserting learning scheme, restarts and no clause deletion.

**Theorem.** Let $\phi$ be a CNF formula in $n$ variables and let $\pi$ be a resolution refutation of $\phi$. Then $\phi$ has a CDCL refutation of size $O(n^3 |\pi|)$. Consequently CDCL, viewed as a proof system, and resolution are polynomially equivalent: every CDCL refutation contains resolution derivations of its learned clauses, and conversely resolution refutations are transformed into CDCL refutations with polynomial overhead.

This improves the $O(n^4 |\pi|)$ bound of Pipatsrisawat and Darwiche (compare [clause learning p-simulates general resolution](../../../propositional-logic/sat-solving/clause-learning-p-simulates-general-resolution.md), which states their p-simulation) for their proof system $\mathrm{CLR}_{\mathrm{LS}}$ ([clause learning as a proof system](../../../propositional-logic/sat-solving/clause-learning-as-a-proof-system.md)), which holds for any asserting learning scheme but, like this result, relies on a decision strategy chosen with knowledge of $\pi$ and on never deleting learned clauses. The two models describe the same solver at different levels: $\mathrm{CLR}_{\mathrm{LS}}$ and its analysis use SAT states, unit resolution, 1-consistency and 1-empowering clauses, while the model here builds natural trails, in which every available unit propagation is made before the next decision and a conflict is taken as soon as one is available. The source notes that the notions do not translate fully: the formula consisting of the single clause $\overline{x}_1 \lor \overline{x}_2 \lor \overline{x}_3$ together with the decisions $x_1, x_2, x_3$ is 1-inconsistent, but no natural trail decides all three, since $\overline{x}_3$ is propagated after $x_1, x_2$. The extra factor $n$ in their bound comes from absorbing every empowering literal of a clause, whereas making a clause unreliable needs only one literal (Section 7 of the source).

## Expansion

Process $\pi$ clause by clause. A clause $C$ is **unreliable** for the current clause database if some natural trail propagates a literal $\ell \in C$ while its set of decision literals is a subset of the negations of the other literals of $C$, that is, $\alpha \subseteq \overline{C} \setminus \{\overline{\ell}\}$; otherwise $C$ is **reliable**. Unreliability needs one such literal, whereas a clause absorbed in the sense of Pipatsrisawat and Darwiche has every literal propagated in this way. If the next clause of $\pi$ is already unreliable, nothing is done. Otherwise one decides the negations of its literals; since it is reliable, these decisions do not block each other, unit propagation runs into a conflict (using the unreliability of its two premises), and the learned asserting clause makes progress. After $O(n^3)$ trail steps the clause becomes unreliable, and one restarts. The empty clause can never become unreliable, so at the latest when $\pi$ reaches $\bot$ the CDCL run learns $\bot$. This is the case of the quantified simulation (Theorem 6.9 of the source, stated on [QCDCL without reduction polynomially simulates Q-resolution](../qbf-proof-complexity/qcdcl-without-reduction-p-simulates-q-resolution.md)) in which every variable is existential: Q-resolution is then resolution, the decision condition imposes no extra restriction, universal reduction is vacuous, and the bound is $O(n^3 |\pi|)$. The constructive variant of Atserias, Fichte and Thurley shows that random decisions suffice when $\phi$ has a refutation of small width.

## Depends on

- [Conflict-driven clause learning as a proof system](cdcl-proof-system.md)
- [Resolution refutation](../../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)

## Proof depends on

- [QCDCL without reduction polynomially simulates Q-resolution](../qbf-proof-complexity/qcdcl-without-reduction-p-simulates-q-resolution.md)

## Sources

- O. Beyersdorff, B. Böhm, "Understanding the relative strength of QBF CDCL solvers and QBF resolution", *Logical Methods in Computer Science* 19(2:2), 2023 (conference version ITCS 2021), doi:10.46298/lmcs-19(2:2)2023, arXiv:2109.04862v5 (Theorem 7.2 and Definition 7.1, Section 7, with the comparison to Pipatsrisawat and Darwiche; reliability is Definition 6.1, and the quantified version is Theorem 6.9 in Section 6).
- J. Nordström, "On the interplay between proof complexity and SAT solving", *ACM SIGLOG News* 2(3), 2015, 19-44, doi:10.1145/2815493.2815497 (Section 3.1).
