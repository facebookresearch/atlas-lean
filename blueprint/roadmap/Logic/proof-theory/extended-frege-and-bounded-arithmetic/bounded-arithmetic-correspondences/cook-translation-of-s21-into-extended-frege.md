# Cook's translation of $S^1_2$-proofs into extended Frege proofs

Every $\Pi^b_1$-sentence provable in $S^1_2$ (or in Cook's theory PV) translates into a family of propositional tautologies with polynomial-size extended Frege proofs, constructible in polynomial time: extended Frege is the non-uniform counterpart of polynomial-time reasoning.

**Translation.** For a bounded formula $\varphi(\bar x)$ there are bounding polynomials such that, for numbers of length at most $n$, the evaluation of $\varphi$ only involves numbers of polynomially bounded length. For a $\Pi^b_1$-formula $\varphi(\bar x)$ and $n\ge 1$, $\lVert\varphi(\bar x)\rVert_n$ is a propositional formula of size polynomial in $n$ whose atoms stand for the bits of $\bar x$ (and, possibly, auxiliary bits); it is a tautology if and only if $\varphi(\bar a)$ holds for all $\bar a$ of length at most $n$.

**Theorem (Cook; Buss).** Let $\varphi(\bar x)$ be a $\Pi^b_1$-formula. If $S^1_2\vdash\forall\bar x\,\varphi(\bar x)$, then the tautologies $\lVert\varphi(\bar x)\rVert_n$ have extended Frege proofs of size polynomial in $n$, and these proofs can be constructed in time polynomial in $n$.

More generally, if $\Phi$ is a polynomial-time decidable set of true $\Pi^b_1$-formulas, then for every $\Pi^b_1$-formula $\psi$ with $S^1_2+\Phi\vdash\forall\bar x\,\psi(\bar x)$, proofs of $\lVert\psi(\bar x)\rVert_n$ in the system $EF+\lVert\Phi\rVert$ can be constructed in polynomial time.

## Expansion

The proof has three steps. First, $S^1_2$ is formulated in a sequent calculus with rules for bounded quantifiers, BASIC axioms as initial sequents, and a $\Sigma^b_1$-PIND rule. Second, by free-cut elimination one may assume that every formula in a proof of $\forall\bar x\,\varphi$ is $\Sigma^b_1$ or $\Pi^b_1$. Third, each sequent is translated with a common bounding polynomial: terms become polynomial-size circuits written with extension variables, sharply bounded quantifiers become polynomial conjunctions and disjunctions, and the existential witnesses of $\Sigma^b_1$ formulas become extension variables; logical axioms and BASIC axioms get polynomial-size proofs, contractions and cuts are handled by redefining witness variables with the extension rule, and an application of PIND is unfolded into a polynomial number of cuts. Cook proved the original version for the equational theory PV in 1975; generalizations are due to Dowd and to Krajíček and Pudlák.

## Depends on

- [Buss's bounded arithmetic theories $S^i_2$ and $T^i_2$](buss-theories-s2i-and-t2i.md)
- [Extended Frege proof systems](../extended-and-substitution-frege/extended-frege-system.md)

## Proof depends on

None.

## Sources

- Olaf Beyersdorff, "On the correspondence between arithmetic theories and propositional proof systems – a survey", *Mathematical Logic Quarterly* 55(2):116–137, 2009, doi:10.1002/malq.200710069 (Section 6: bounding polynomials and the translation $\lVert\cdot\rVert$; Section 10: Theorem 10.1 (Cook, Buss) and Corollary 10.2; pre-review numbering).
- Samuel R. Buss, *Bounded arithmetic and propositional proofs, Part II: propositional proofs and two translations from bounded arithmetic*, lecture notes, <https://people.cs.rutgers.edu/~allender/lecture.notes/buss.part2.pdf> (slides 8 to 18: Cook's 1975 theorem for PV, its $S^1_2$ version, the definitions of bounding polynomials and of the translation, and the proof by free-cut elimination).
- Paul Beame and Toniann Pitassi, "Propositional proof complexity: past, present, and future", *Bulletin of the EATCS* 65, 1998; reprinted in *Current Trends in Theoretical Computer Science*, World Scientific, 2001, <https://mathweb.ucsd.edu/~sbuss/CourseWeb/Math268_2014W/BeamePitassi_pastpresentfuture.pdf> (Section 2.3: Cook's connection between polynomial-size extended Frege proofs and polynomial-time reasoning in PV or $S^1_2$).
