# $V^0$ and $VNC^1$ correspond to bounded-depth Frege and Frege

The two-sorted theory $V^0$ (for $\mathsf{AC}^0$) proves the soundness of bounded-depth Frege, and its $\Sigma^B_0$-theorems translate into polynomial-size bounded-depth Frege proofs; $VNC^1$ (for $\mathsf{NC}^1$) plays the same role for Frege.

The theories $V^0$ and $VNC^1$, the classes $\Sigma^B_i$ and the predicates $\mathrm{Fla}$, $\vDash$, $\mathrm{Taut}$, $\mathrm{Prf}_{F_d}$ and $\mathrm{Prf}_F$ are as on [the two-sorted theories page](two-sorted-theories-v0-and-vnc1.md); $\mathrm{Ref}_F$ is the two-sorted [reflection principle](../optimal-proof-systems-and-incompleteness/reflection-principle-of-a-proof-system.md) for Frege.

**Theorem.** (a) $V^0$ proves, for every $d$, the soundness of depth-$d$ Frege: $\forall A\,\forall\Pi\,(\mathrm{Prf}_{F_d}(\Pi,A)\to\mathrm{Taut}(A))$. (b) $VNC^1$ proves the soundness of Frege. (c) If $\varphi(\bar x,\bar X)$ is $\Sigma^B_0$ and $V^0\vdash\forall\bar X\,\forall\bar x\,\varphi$, then the propositional translations $\llbracket\varphi\rrbracket_{\bar m,\bar n}$ have bounded-depth Frege proofs of length polynomial in $\max(\bar m,\bar n)$; if $VNC^1\vdash\forall\bar X\,\forall\bar x\,\varphi$, they have polynomial-length Frege proofs. These proofs are computable in polynomial time from $(\bar m,\bar n)$. (d) If $V^0\vdash\mathrm{Ref}_F$, then bounded-depth Frege p-simulates Frege.

The translation $\llbracket\cdot\rrbracket$ evaluates atomic number formulas, turns string atoms into propositional variables, and turns bounded number quantifiers into conjunctions and disjunctions.

## Expansion

Parts (a) to (c) are the two-sorted form of the correspondence between theories and proof systems, developed by Cook and Nguyen. Part (d) follows the pattern of the $S^1_2$/extended Frege case: translating the $V^0$-proof of $\mathrm{Ref}_F$ gives bounded-depth Frege proofs of its translations; bounded-depth Frege can verify an encoding of the computation checking a given Frege proof, and cut with the translated reflection principle yields the translation of $\mathrm{Taut}(\varphi)$ and then $\varphi$.

## Depends on

- [The two-sorted theories $V^0$ and $VNC^1$](two-sorted-theories-v0-and-vnc1.md)
- [Frege proof systems](../extended-and-substitution-frege/frege-system.md)
- [Reflection principle of a propositional proof system](../optimal-proof-systems-and-incompleteness/reflection-principle-of-a-proof-system.md)
- [Cook–Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Proof depends on

None.

## Sources

- Sebastian Müller, "Polylogarithmic cuts in models of V^0", *Logical Methods in Computer Science* 9(1):16, 2013, doi:10.2168/LMCS-9(1:16)2013, arXiv:1303.6075v2 (Section 2.4: Definition 2.5, Facts 2.4 to 2.6, Definition 2.6, the propositional translation, and Theorem 2.1 with its proof sketch).
