# Extended Frege is the proof system of $S^1_2$

$S^1_2$ proves the soundness of extended Frege, and extended Frege p-simulates every propositional proof system whose soundness $S^1_2$ proves. Thus extended Frege is the strongest proof system that $S^1_2$ can verify (Krajíček and Pudlák).

**Theorem (Krajíček–Pudlák).**

1. $S^1_2\vdash\mathrm{RFN}(EF)$.
2. If $P$ is a propositional proof system with $S^1_2\vdash\mathrm{RFN}(P)$, then $EF$ p-simulates $P$.
3. More generally, for a polynomial-time decidable set $\Phi$ of true $\Pi^b_1$-formulas: $S^1_2+\Phi\vdash\mathrm{RFN}(EF+\lVert\Phi\rVert)$; if $S^1_2+\Phi\vdash\mathrm{RFN}(P)$ then $EF+\lVert\Phi\rVert$ p-simulates $P$; and $EF+\lVert\Phi\rVert$ is strongly regular, corresponds to the theory $S^1_2+\Phi$, and has the strong reflection property.

Consequences: $EF$ has polynomial-size proofs of the propositional consistency statements $\lVert\mathrm{Con}(EF)\rVert_n$, and $EF$ p-simulates substitution Frege because $S^1_2\vdash\mathrm{RFN}(SF)$.

## Expansion

For (1), fix an $EF$-proof $\varphi_1,\dots,\varphi_n$ with extension variables $\bar q$ and argue in $S^1_2$ by induction on $i$ (polynomial induction on the code of the proof, which allows induction on the number of lines) that every assignment $\alpha$ to the original variables extends to an assignment $\beta$ of $\bar q$ satisfying $\varphi_1,\dots,\varphi_i$; since extension variables do not occur in the conclusion, $\alpha\vDash\varphi_n$. For (2), given a $P$-proof $\pi$ of $\varphi$, apply [Cook's translation](cook-translation-of-s21-into-extended-frege.md) to the $S^1_2$-proof of $\mathrm{RFN}(P)$: $EF$ gets polynomial-size proofs of $\lVert\mathrm{RFN}(P)\rVert_n$, verifies the computation $P(\pi)=\varphi$ by substituting the bits of $\pi$ and $\varphi$, concludes the translation of $\mathrm{Taut}(\varphi)$, and derives $\varphi$ from it by a polynomial-size $EF$-proof (Krajíček–Pudlák's lemma that $EF$ proves $\lVert\mathrm{Taut}(\varphi)\rVert\to\varphi$). Together with Cook's translation this is the general correspondence between theories and proof systems: the theory proves the soundness of its proof system, and the proof system has short proofs of the theory's $\forall\Pi^b_1$-consequences.

## Depends on

- [Buss's bounded arithmetic theories $S^i_2$ and $T^i_2$](buss-theories-s2i-and-t2i.md)
- [Extended Frege proof systems](../extended-and-substitution-frege/extended-frege-system.md)
- [Reflection principle of a propositional proof system](../optimal-proof-systems-and-incompleteness/reflection-principle-of-a-proof-system.md)

## Proof depends on

- [Cook's translation of $S^1_2$-proofs into extended Frege proofs](cook-translation-of-s21-into-extended-frege.md)
- [Buss's witnessing theorem](buss-witnessing-theorem.md)

## Sources

- Olaf Beyersdorff, "On the correspondence between arithmetic theories and propositional proof systems – a survey", *Mathematical Logic Quarterly* 55(2):116–137, 2009, doi:10.1002/malq.200710069 (Section 9: properties 1 to 6 of the correspondence and the remark that $SF\le EF$ follows from $S^1_2\vdash\mathrm{RFN}(SF)$; Section 10: Lemma 10.3, Theorem 10.4, Corollary 10.6, Theorems 10.7, 10.8 and 10.9; pre-review numbering).
- Samuel R. Buss, *Bounded arithmetic and propositional proofs, Part II: propositional proofs and two translations from bounded arithmetic*, lecture notes, <https://people.cs.rutgers.edu/~allender/lecture.notes/buss.part2.pdf> (slides 19 and 20: Theorems A to C after Cook, including polynomial-size $eF$-proofs of $\mathrm{Con}_{eF}(n)$ and the p-simulation of systems whose consistency $S^1_2$ proves).
