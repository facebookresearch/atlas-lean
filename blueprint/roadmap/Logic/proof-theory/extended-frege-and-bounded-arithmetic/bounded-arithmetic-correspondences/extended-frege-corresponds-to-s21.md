# Extended Frege is the proof system of $S^1_2$

$S^1_2$ proves the soundness of extended Frege, and extended Frege p-simulates every propositional proof system whose soundness $S^1_2$ proves. Thus extended Frege is the strongest proof system that $S^1_2$ can verify (Krajíček and Pudlák).

**Theorem (Krajíček–Pudlák).**

1. $S^1_2\vdash\mathrm{RFN}(EF)$.
2. If $P$ is a propositional proof system with $S^1_2\vdash\mathrm{RFN}(P)$, then $EF$ p-simulates $P$.
3. More generally, let $\Phi$ be a polynomial-time decidable set of true $\Pi^b_1$-formulas, $T=S^1_2+\Phi$, and $EF+\lVert\Phi\rVert$ the system $EF$ in which the translations $\lVert\varphi\rVert_n$ ($\varphi\in\Phi$, $n\ge0$) and their substitution instances may be used as additional axioms. Then $EF+\lVert\Phi\rVert$ and $T$ satisfy:
   - for every $\Pi^b_1$-formula $\psi(x)$ with $T\vdash\forall x\,\psi(x)$, a polynomial-time function outputs on input $1^n$ an $EF+\lVert\Phi\rVert$-proof of $\lVert\psi(x)\rVert_n$;
   - $T\vdash\mathrm{RFN}(EF+\lVert\Phi\rVert)$, and if $T\vdash\mathrm{RFN}(P)$ for a propositional proof system $P$, then $EF+\lVert\Phi\rVert$ p-simulates $P$.

   In Beyersdorff's terms, these two conditions say that $EF+\lVert\Phi\rVert$ is *strongly regular* (Definition 9.2) with $T$ as the witnessing theory. In particular $EF+\lVert\Phi\rVert$ has the strong reflection property.

## Expansion

For (1), fix an $EF$-proof $\varphi_1,\dots,\varphi_n$ with extension variables $\bar q$ and argue in $S^1_2$ by induction on $i$ (polynomial induction on the code of the proof, which allows induction on the number of lines) that every assignment $\alpha$ to the original variables extends to an assignment $\beta$ of $\bar q$ satisfying $\varphi_1,\dots,\varphi_i$; since extension variables do not occur in the conclusion, $\alpha\vDash\varphi_n$. For (2), given a $P$-proof $\pi$ of $\varphi$, apply [Cook's translation](cook-translation-of-s21-into-extended-frege.md) to the $S^1_2$-proof of $\mathrm{RFN}(P)$: $EF$ gets polynomial-size proofs of $\lVert\mathrm{RFN}(P)\rVert_n$, verifies the computation $P(\pi)=\varphi$ by substituting the bits of $\pi$ and $\varphi$, concludes the translation of $\mathrm{Taut}(\varphi)$, and derives $\varphi$ from it by a polynomial-size $EF$-proof (Krajíček–Pudlák's lemma that $EF$ proves $\lVert\mathrm{Taut}(\varphi)\rVert\to\varphi$). Together with Cook's translation this is the general correspondence between theories and proof systems: the theory proves the soundness of its proof system, and the proof system has short proofs of the theory's $\forall\Pi^b_1$-consequences. Two consequences recorded by the sources: $EF$ has polynomial-size proofs of the propositional consistency statements $\lVert\mathrm{Con}(EF)\rVert_n$, and $EF$ p-simulates substitution Frege because $S^1_2\vdash\mathrm{RFN}(SF)$.

## Depends on

- [Buss's bounded arithmetic theories $S^i_2$ and $T^i_2$](buss-theories-s2i-and-t2i.md)
- [Extended Frege proof systems](../extended-and-substitution-frege/extended-frege-system.md)
- [Reflection principle of a propositional proof system](../optimal-proof-systems-and-incompleteness/reflection-principle-of-a-proof-system.md)

## Proof depends on

- [Cook's translation of $S^1_2$-proofs into extended Frege proofs](cook-translation-of-s21-into-extended-frege.md)
- [Buss's witnessing theorem](buss-witnessing-theorem.md)

## Sources

- Olaf Beyersdorff, "On the correspondence between arithmetic theories and propositional proof systems – a survey", *Mathematical Logic Quarterly* 55(2):116–137, 2009, doi:10.1002/malq.200710069 (Section 3: extensions $EF+\Phi$ by polynomial-time sets of axioms and their substitution instances; Section 6: $\lVert\varphi(x)\rVert=\{\lVert\varphi(x)\rVert_n : n\ge 0\}$; Section 9: properties 1 to 6 of the correspondence, Definition 9.2 of strongly regular systems, and the remark that $SF\le EF$ follows from $S^1_2\vdash\mathrm{RFN}(SF)$; Section 10: Lemma 10.3, Theorem 10.4, Corollary 10.6, Theorems 10.7, 10.8 and 10.9; numbering of the author's pre-review version deposited at White Rose Research Online, <https://eprints.whiterose.ac.uk/id/eprint/74440/>).
- Samuel R. Buss, "Bounded arithmetic and propositional proof complexity", in *Logic of Computation* (H. Schwichtenberg, ed.), Springer, 1997, author's copy <https://mathweb.ucsd.edu/~sbuss/ResearchWeb/marktoberdorf95/paper.pdf> (Section 6.2: Theorem 31, $eF$ p-simulates every system $G\supseteq F$ whose consistency $S^1_2$ proves, and Theorem 33, polynomial-size $eF$-proofs of $\mathrm{Con}_{eF}(n)$, both due to Cook).
