# Reflection principle of a propositional proof system

The reflection principle $\mathrm{RFN}(P)$ of a propositional proof system $P$ is the arithmetic sentence stating that every formula with a $P$-proof is a tautology. $P$ has the reflection property if the propositional translations of $\mathrm{RFN}(P)$ have polynomial-size $P$-proofs.

Work in Buss's language of bounded arithmetic, with $\Delta^b_1$-formalizations (with respect to $S^1_2$) of the relations $\mathrm{Prf}_P(\pi,\varphi)$, "$\pi$ is a $P$-proof of $\varphi$", and $\mathrm{Taut}(\varphi)$, "every assignment satisfies $\varphi$". Define

$$
\mathrm{Con}(P) \;=\; (\forall\pi)\,\neg\mathrm{Prf}_P(\pi,\bot), \qquad \mathrm{RFN}(P) \;=\; (\forall\pi)(\forall\varphi)\,\big(\mathrm{Prf}_P(\pi,\varphi)\to\mathrm{Taut}(\varphi)\big).
$$

Both are $\forall\Pi^b_1$-sentences. Writing $\lVert\cdot\rVert_n$ for the propositional translation of $\Pi^b_1$-formulas at input length $n$:

- $P$ has the *reflection property* if $\lVert\mathrm{RFN}(P)\rVert_n$ has $P$-proofs of size polynomial in $n$;
- $P$ has the *strong reflection property* if a polynomial-time algorithm outputs a $P$-proof of $\lVert\mathrm{RFN}(P)\rVert_n$ on input $1^n$.

Both properties refer to some polynomial-time machine computing $P$ with a suitable $\Delta^b_1$-formalization of its computation. Facts from the source: if $P$ is closed under substitutions and modus ponens, evaluates variable-free formulas, and these properties are provable in $S^1_2$, then $S^1_2\vdash\mathrm{RFN}(P)\leftrightarrow\mathrm{Con}(P)$; and p-equivalent proof systems have (strong) reflection simultaneously.

In two-sorted bounded arithmetic over $V^0$, the reflection principle $\mathrm{Ref}_P$ is the $\forall\Delta^B_1$-formula $\forall\Pi\,\forall X\,\forall Z\,\big((\mathrm{Fla}(X)\wedge\mathrm{Prf}_P(\Pi,X))\to Z\vDash X\big)$.

## Expansion

Reflection condenses the strength of a proof system: proving $\mathrm{RFN}(Q)$ in the theory that corresponds to $P$ yields a simulation of $Q$ by $P$, and $\lVert\mathrm{RFN}(Q)\rVert_n$ is a natural candidate hard sequence for $P$ whenever $Q$ is not simulated by $P$. The equivalence with consistency fails for arbitrary Cook–Reckhow systems, which is why the closure conditions are listed.

## Depends on

- [Cook–Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)
- [Buss's bounded arithmetic theories $S^i_2$ and $T^i_2$](../bounded-arithmetic-correspondences/buss-theories-s2i-and-t2i.md)
- [Cook's translation of $S^1_2$-proofs into extended Frege proofs](../bounded-arithmetic-correspondences/cook-translation-of-s21-into-extended-frege.md)

## Proof depends on

None.

## Sources

- Olaf Beyersdorff, "On the correspondence between arithmetic theories and propositional proof systems – a survey", *Mathematical Logic Quarterly* 55(2):116–137, 2009, doi:10.1002/malq.200710069 (Section 8: $\mathrm{Con}(P)$ and $\mathrm{RFN}(P)$, Proposition 8.1, Definitions 8.2 and 8.3, Proposition 8.4; pre-review numbering).
- Sebastian Müller, "Polylogarithmic cuts in models of V^0", *Logical Methods in Computer Science* 9(1):16, 2013, doi:10.2168/LMCS-9(1:16)2013, arXiv:1303.6075v2 (Section 2.4: Definition 2.6, the reflection principle $\mathrm{Ref}_P$ over $V^0$).
