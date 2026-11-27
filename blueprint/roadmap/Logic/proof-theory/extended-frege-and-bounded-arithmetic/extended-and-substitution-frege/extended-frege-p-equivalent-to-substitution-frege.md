# Extended Frege and substitution Frege are p-equivalent

Extended Frege and substitution Frege systems polynomially simulate each other. Substitution Frege p-simulates extended Frege directly (Cook and Reckhow); the converse, due to Dowd and to Krajíček and Pudlák, follows because $S^1_2$ proves the soundness of substitution Frege.

**Theorem.** Let $EF$ and $SF$ be the extended Frege and substitution Frege systems over a common Frege system. Then $EF \equiv_p SF$: there are polynomial-time computable functions that map every $EF$-proof of a formula $\varphi$ to an $SF$-proof of $\varphi$, and every $SF$-proof of $\varphi$ to an $EF$-proof of $\varphi$.

Here a proof system $S$ p-simulates $P$ if a polynomial-time function maps $P$-proofs to $S$-proofs of the same formula, and p-equivalence means p-simulation in both directions.

## Expansion

*$SF$ p-simulates $EF$.* Given an $EF$-proof with extension lines $A_1\leftrightarrow\beta_1,\dots,A_h\leftrightarrow\beta_h$, read it as a Frege derivation of the conclusion $\alpha$ from these premises, deduce the implication from their conjunction to $\alpha$, and then use the substitution rule to replace $A_h$ by $\beta_h$, then $A_{h-1}$ by $\beta_{h-1}$ and so on; each substituted premise becomes a trivially provable equivalence $\beta_i\leftrightarrow\beta_i$ and can be discharged. The freshness conditions on the $A_i$ guarantee that the substitutions do not touch $\alpha$.

*$EF$ p-simulates $SF$.* The direct propositional simulation is involved. The route through bounded arithmetic is short: Buss's theory $S^1_2$ proves the reflection principle $\mathrm{RFN}(SF)$, by induction on the number of proof lines, and [every proof system whose reflection principle $S^1_2$ proves is p-simulated by $EF$](../bounded-arithmetic-correspondences/extended-frege-corresponds-to-s21.md).

The same equivalence lifts to deep inference: extended and substitution versions of the calculus-of-structures system $SKSg$ are p-equivalent to these systems.

## Depends on

- [Frege proof systems](frege-system.md)
- [Extended Frege proof systems](extended-frege-system.md)
- [Substitution Frege proof systems](substitution-frege-system.md)

## Proof depends on

- [Reflection principle of a propositional proof system](../optimal-proof-systems-and-incompleteness/reflection-principle-of-a-proof-system.md)
- [Extended Frege is the proof system of $S^1_2$](../bounded-arithmetic-correspondences/extended-frege-corresponds-to-s21.md)

## Sources

- Paul Beame and Toniann Pitassi, "Propositional proof complexity: past, present, and future", *Bulletin of the EATCS* 65, 1998; reprinted in *Current Trends in Theoretical Computer Science*, World Scientific, 2001; ECCC report TR98-067, <https://eccc.weizmann.ac.il/report/1998/067/> (Section 2.1: extended Frege proofs are p-equivalent to substitution Frege proofs, by Dowd and by Krajíček and Pudlák).
- Olaf Beyersdorff, "On the correspondence between arithmetic theories and propositional proof systems – a survey", *Mathematical Logic Quarterly* 55(2):116–137, 2009, doi:10.1002/malq.200710069 (Section 3: $EF$ is simulated by $SF$ (Cook and Reckhow), the converse by Dowd and by Krajíček and Pudlák; Section 9: $SF \le EF$ follows from $S^1_2 \vdash \mathrm{RFN}(SF)$; numbering of the author's pre-review version deposited at White Rose Research Online, <https://eprints.whiterose.ac.uk/id/eprint/74440/>).
- Paola Bruscoli and Alessio Guglielmi, "On the proof complexity of deep inference", *ACM Transactions on Computational Logic* 10(2):14, 2009, doi:10.1145/1462179.1462186, arXiv:0709.1201v3 (Theorem 5.8: $xFrege$ and $sFrege$ are p-equivalent, attributed to Cook–Reckhow and Krajíček–Pudlák).
- Samuel R. Buss, "Bounded arithmetic and propositional proof complexity", in *Logic of Computation* (H. Schwichtenberg, ed.), Springer, 1997, author's copy <https://mathweb.ucsd.edu/~sbuss/ResearchWeb/marktoberdorf95/paper.pdf> (Section 6.2: Theorem 35 (Cook and Reckhow; Dowd; Krajíček and Pudlák), $sF$ and $eF$ p-simulate each other, with $eF$ p-simulating $sF$ since $S^1_2\vdash\mathrm{Con}(sF)$).
