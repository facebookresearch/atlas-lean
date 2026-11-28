# Reflection principle of a propositional proof system

The reflection principle $\mathrm{RFN}(P)$ of a propositional proof system $P$ is the arithmetic sentence stating that every formula with a $P$-proof is a tautology. $P$ has the reflection property if the propositional translations of $\mathrm{RFN}(P)$ have polynomial-size $P$-proofs.

Work in Buss's language of bounded arithmetic. Let $\mathrm{Prf}_P(\pi,\varphi)$, "$\pi$ is a $P$-proof of $\varphi$", be a $\Delta^b_1$-formalization with respect to $S^1_2$. Let $\mathrm{Assign}(\alpha,\varphi)$ be the $\Sigma^b_0$-formula saying that $\alpha$ codes an assignment to the variables of $\varphi$, and let $\alpha\vDash\varphi$ be the formula saying that $\alpha$ satisfies $\varphi$, which is $\Delta^b_1$ with respect to $S^1_2$. Then $\mathrm{Taut}(\varphi)$ is the $\Pi^b_1$-formula $(\forall\alpha)\,(\mathrm{Assign}(\alpha,\varphi)\to\alpha\vDash\varphi)$, "every assignment satisfies $\varphi$". Define

$$
\mathrm{Con}(P) \;=\; (\forall\pi)\,\neg\mathrm{Prf}_P(\pi,\bot), \qquad \mathrm{RFN}(P) \;=\; (\forall\pi)(\forall\varphi)\,\big(\mathrm{Prf}_P(\pi,\varphi)\to\mathrm{Taut}(\varphi)\big).
$$

Both are $\forall\Pi^b_1$-sentences. Writing $\lVert\cdot\rVert_n$ for the propositional translation of $\Pi^b_1$-formulas at input length $n$:

- $P$ has the *reflection property* if $\lVert\mathrm{RFN}(P)\rVert_n$ has $P$-proofs of size polynomial in $n$;
- $P$ has the *strong reflection property* if a polynomial-time algorithm outputs a $P$-proof of $\lVert\mathrm{RFN}(P)\rVert_n$ on input $1^n$.

Both properties refer to some polynomial-time machine computing $P$ with a suitable $\Delta^b_1$-formalization of its computation. Facts from the source: if $P$ is closed under substitutions and modus ponens, evaluates variable-free formulas, and these properties are provable in $S^1_2$, then $S^1_2\vdash\mathrm{RFN}(P)\leftrightarrow\mathrm{Con}(P)$; and p-equivalent proof systems have (strong) reflection simultaneously.

In two-sorted bounded arithmetic over [$V^0$](../bounded-arithmetic-correspondences/two-sorted-theories-v0-and-vnc1.md), with the predicates $\mathrm{Fla}$, $\vDash$ and $\mathrm{Prf}_P$ defined there, the reflection principle $\mathrm{Ref}_P$ is the $\forall\Delta^B_1$-formula (with respect to $V^0$) $\forall\Pi\,\forall X\,\forall Z\,\big((\mathrm{Fla}(X)\wedge\mathrm{Prf}_P(\Pi,X))\to Z\vDash X\big)$.

## Expansion

Reflection condenses the strength of a proof system: proving $\mathrm{RFN}(Q)$ in the theory that corresponds to $P$ yields a simulation of $Q$ by $P$, and $\lVert\mathrm{RFN}(Q)\rVert_n$ is a natural candidate hard sequence for $P$ whenever $Q$ is not simulated by $P$. The equivalence with consistency fails for arbitrary Cook–Reckhow systems, which is why the closure conditions are listed.

## Depends on

- [Cook–Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)
- [Buss's bounded arithmetic theories $S^i_2$ and $T^i_2$](../bounded-arithmetic-correspondences/buss-theories-s2i-and-t2i.md)
- [Cook's translation of $S^1_2$-proofs into extended Frege proofs](../bounded-arithmetic-correspondences/cook-translation-of-s21-into-extended-frege.md)
- [The two-sorted theories $V^0$ and $VNC^1$](../bounded-arithmetic-correspondences/two-sorted-theories-v0-and-vnc1.md)

## Proof depends on

None.

## Sources

- Olaf Beyersdorff, "On the correspondence between arithmetic theories and propositional proof systems – a survey", *Mathematical Logic Quarterly* 55(2):116–137, 2009, doi:10.1002/malq.200710069 (Section 7: the formulas $\mathrm{Assign}$, $\alpha\vDash\varphi$ ($\Delta^b_1$ with respect to $S^1_2$), $\mathrm{Taut}$ ($\Pi^b_1$) and $\mathrm{Prf}_P$ ($\Delta^b_1$ with respect to $S^1_2$); Section 8: $\mathrm{Con}(P)$ and $\mathrm{RFN}(P)$, Proposition 8.1, Definitions 8.2 and 8.3, Proposition 8.4; numbering of the author's pre-review version deposited at White Rose Research Online, <https://eprints.whiterose.ac.uk/id/eprint/74440/>).
- Sebastian Müller, "Polylogarithmic cuts in models of V^0", *Logical Methods in Computer Science* 9(1):16, 2013, doi:10.2168/LMCS-9(1:16)2013, arXiv:1303.6075v2 (Section 2.4: Definition 2.6, the reflection principle $\mathrm{Ref}_P$ over $V^0$).
