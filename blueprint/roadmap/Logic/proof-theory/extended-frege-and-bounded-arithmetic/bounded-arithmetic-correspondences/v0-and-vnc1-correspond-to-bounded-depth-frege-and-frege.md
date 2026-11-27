# $V^0$ and $VNC^1$ correspond to bounded-depth Frege and Frege

The two-sorted theory $V^0$ (for $\mathsf{AC}^0$) proves the soundness of bounded-depth Frege, and its $\Sigma^B_0$-theorems translate into polynomial-size bounded-depth Frege proofs; $VNC^1$ (for $\mathsf{NC}^1$) plays the same role for Frege.

**Theories.** Two-sorted bounded arithmetic has number variables and string (finite set) variables $X$ with length $|X|$. $V^0$ consists of the twelve basic axioms of $\mathrm{PA}^-$ for $0,1,+,\cdot,\le$, the axioms $X(y)\to y<|X|$ and $y+1=|X|\to X(y)$, string extensionality, and the comprehension scheme

$$
\Sigma^B_0\text{-COMP}:\quad \exists X\le y\ \forall z<y\ \big(X(z)\leftrightarrow\varphi(z)\big)\qquad(\varphi\in\Sigma^B_0);
$$

it proves $\Sigma^B_0$-induction. $VNC^1$ is $V^0$ plus the axiom MFV stating that every monotone formula, given as a tree $G$ of $\wedge$/$\vee$ nodes with an input assignment $I$, has an evaluation string $Y$ of length at most $2a+1$ satisfying the local evaluation conditions.

**Theorem.** (a) $V^0$ proves, for every $d$, the soundness of depth-$d$ Frege: $\forall A\,\forall\Pi\,(\mathrm{Prf}_{F_d}(\Pi,A)\to\mathrm{Taut}(A))$. (b) $VNC^1$ proves the soundness of Frege. (c) If $\varphi(\bar x,\bar X)$ is $\Sigma^B_0$ and $V^0\vdash\forall\bar X\,\forall\bar x\,\varphi$, then the propositional translations $\llbracket\varphi\rrbracket_{\bar m,\bar n}$ have bounded-depth Frege proofs of length polynomial in $\max(\bar m,\bar n)$; if $VNC^1\vdash\forall\bar X\,\forall\bar x\,\varphi$, they have polynomial-length Frege proofs. These proofs are computable in polynomial time from $(\bar m,\bar n)$. (d) If $V^0$ proves the reflection principle for Frege, then bounded-depth Frege p-simulates Frege.

The translation $\llbracket\cdot\rrbracket$ evaluates atomic number formulas, turns string atoms into propositional variables, and turns bounded number quantifiers into conjunctions and disjunctions.

## Expansion

Parts (a) to (c) are the two-sorted form of the correspondence between theories and proof systems, developed by Cook and Nguyen. Part (d) follows the pattern of the $S^1_2$/extended Frege case: translating the $V^0$-proof of $\mathrm{Ref}_F$ gives bounded-depth Frege proofs of its translations; bounded-depth Frege can verify an encoding of the computation checking a given Frege proof, and cut with the translated reflection principle yields the translation of $\mathrm{Taut}(\varphi)$ and then $\varphi$. MFV is not provable in $V^0$, since witnessing would put monotone $\mathsf{NC}^1$ in $\mathsf{AC}^0$. Related theories form the chain $V^0\subset V^0(2)\subset VTC^0\subseteq VNC^1\subseteq VL\subseteq\cdots\subseteq VP$, where $V^0(2)$ adds a parity axiom and $VTC^0$ a counting axiom, and their $\Sigma^B_1$-definable functions are exactly $\mathsf{FAC}^0$, $\mathsf{FAC}^0(2)$ and $\mathsf{FTC}^0$.

## Depends on

- [Cook–Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Proof depends on

None.

## Sources

- Sebastian Müller, "Polylogarithmic cuts in models of V^0", *Logical Methods in Computer Science* 9(1):16, 2013, doi:10.2168/LMCS-9(1:16)2013, arXiv:1303.6075v2 (Section 2.2: axioms of $V^0$ and Fact 2.3; Section 2.3: $VNC^1$ and MFV; Section 2.4: Definition 2.5, Facts 2.4 to 2.6, Definition 2.6 and Theorem 2.1).
- Stephen A. Cook and Lila Fontes, "Formal theories for linear algebra", *Logical Methods in Computer Science* 8(1):25, 2012, doi:10.2168/LMCS-8(1:25)2012, arXiv:1101.1449v4 (Section 1: the chain (1.4) of theories; Section 2: Definitions 2.11 and 2.12 of $V^0(2)$ and $VTC^0$ and Proposition 2.13 on their definable functions).
