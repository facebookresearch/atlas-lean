# Bounded-depth Frege subexponentially simulates Frege

Every Frege proof can be converted into a bounded-depth Frege proof of subexponential size: for every depth bound and $\delta>0$ some larger depth gives proofs of size $2^{m^{\delta}}$ (Filmus, Pitassi and Santhanam; reproved by Müller via cuts of models of $V^0$).

A proof system $P$ *subexponentially simulates* $Q$ if there is a function $f$ in a class of $2^{n^{o(1)}}$ functions such that every tautology with a $Q$-proof $\pi_Q$ has a $P$-proof of size at most $f(|\pi_Q|)$.

**Theorem.** Every Frege system is subexponentially simulated by bounded-depth Frege. More precisely, for all $D>1$ and $\delta>0$ there is $d\ge D$ such that every formula of depth $D$ with a Frege proof of length $m$ has a depth-$d$ Frege proof of length at most $2^{m^{\delta}}$, and this proof can be computed efficiently from the Frege proof.

**Same method.** Bounded-depth Frege subexponentially simulates $TC^0$-Frege (Bonet, Domingo, Gavaldà, Maciel and Pitassi).

## Expansion

If $V^0\vdash\mathrm{Ref}_F(t(x))$, the reflection principle for Frege proofs of size at most $t(x)$, with $t(x)<x$ for large $x$, then Frege proofs of length $t(x)$ convert into bounded-depth Frege proofs of length $x^{O(1)}$; taking $t(x)=|x|^k$ for every $k$ gives the subexponential bound. Bounded reflection with polylogarithmic proof length in $V^0$ is the same as full reflection inside the polylogarithmic cut of a model of $V^0$, which is a model of $VNC^1$, and $VNC^1$ proves the soundness of Frege. For $TC^0$-Frege the same argument uses that the cut also satisfies $VTC^0$.

## Depends on

- [Cook–Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Proof depends on

- [$V^0$ and $VNC^1$ correspond to bounded-depth Frege and Frege](v0-and-vnc1-correspond-to-bounded-depth-frege-and-frege.md)
- [Polylogarithmic cuts of models of $V^0$ satisfy $VNC^1$](polylogarithmic-cuts-of-v0-models-satisfy-vnc1.md)

## Sources

- Sebastian Müller, "Polylogarithmic cuts in models of V^0", *Logical Methods in Computer Science* 9(1):16, 2013, doi:10.2168/LMCS-9(1:16)2013, arXiv:1303.6075v2 (Section 2.1: Definition 2.3 of subexponential simulation; Section 2.4: Definition 2.7, Theorem 2.2 and Corollary 2.3; Section 4: Theorem 4.1 (Filmus, Pitassi and Santhanam) and its proof; Section 1: the $TC^0$-Frege simulation of Bonet, Domingo, Gavaldà, Maciel and Pitassi).
