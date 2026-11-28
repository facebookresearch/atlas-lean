# Second-order unification with one function variable and eight individual variables is undecidable

Second-order unification remains undecidable for problems containing a single function variable, provided at least eight first-order (individual) variables may occur.

**Theorem (Ganzinger, Jacquemard and Veanes).** [Second-order unification](second-order-unification-problems.md), with syntactic equality, is undecidable for problems in which exactly one function variable occurs and at least eight individual variables occur: no algorithm decides whether such a problem has a unifier.

Other known undecidable fragments include problems with two function variables and no individual variables, and problems with one function variable applied only to ground arguments together with individual variables (Levy and Veanes), as reported by the source.

## Depends on

- [Second-order unification problems](second-order-unification-problems.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The result was obtained in the study of rigid reachability, the non-symmetric form of rigid $E$-unification. As Levy and Veanes summarize the proof (Section 7, item 11, of their paper), Ganzinger, Jacquemard and Veanes prove rigid reachability undecidable even for ground systems of rules, and derive the undecidability of second-order unification with a single second-order variable occurring at most twice from it by a translation analogous to Lemma 2 of Levy and Veanes, which relates rigid reachability to second-order unification. A good expansion links pages for the undecidability of rigid reachability for ground rewrite systems and for that translation. It sharpens Goldfarb's undecidability of second-order unification with respect to the number of function variables, at the price of allowing individual variables; whether individual variables are needed at all is the question answered for associative theories by Cerna and Parsert.

## Sources

- H. Ganzinger, F. Jacquemard and M. Veanes, "Rigid reachability", in *Advances in Computing Science (ASIAN 98)*, Lecture Notes in Computer Science 1538, Springer, 1998, pp. 4–21, doi:10.1007/3-540-49366-2_2; journal version "Rigid reachability, the non-symmetric form of rigid E-unification", *International Journal of Foundations of Computer Science* 11:3–27, 2000, doi:10.1142/S012905410000003X (original sources, cited beside the copy read).
- J. Levy and M. Veanes, "On the undecidability of second-order unification", *Information and Computation* 159(1–2):125–150, 2000, doi:[10.1006/inco.2000.2877](https://doi.org/10.1006/inco.2000.2877); read in the authors' copy at <https://www.iiia.csic.es/~levy/papers/sou.pdf>: Lemma 2 of Section 3 and item 11 of Section 7, which summarize the proof.
- D. M. Cerna and J. Parsert, "One is all you need: second-order unification without first-order variables", *Logical Methods in Computer Science* 22(2), paper 3, 2026, doi:10.46298/lmcs-22(2:3)2026; read as arXiv:2404.10616v10, <https://arxiv.org/abs/2404.10616v10>: Section 1, the list of undecidable fragments of second-order unification, which states the result.
