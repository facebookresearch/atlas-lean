# The two-sorted theories $V^0$ and $VNC^1$

$V^0$ is the two-sorted theory of bounded arithmetic for $\mathsf{AC}^0$, with number variables and string variables and comprehension for $\Sigma^B_0$-formulas; $VNC^1$ adds an axiom for evaluating monotone formulas. Over $V^0$ one defines formulas, satisfaction, tautologies and proofs of propositional proof systems.

**Language and formulas.** The language $\mathcal L^2_A$ has number variables $x,y,z,\dots$, string (finite set) variables $X,Y,Z,\dots$, and the symbols $+,\cdot,\le,0,1,|\cdot|,=_1,=_2,\in$, where $|X|$ is the largest element of $X$ plus one and $X(y)$ abbreviates $y\in X$. A number quantifier is bounded if it has the form $\exists x\,(x\le t\wedge\dots)$ or $\forall x\,(x\le t\to\dots)$, and a string quantifier if it has the form $\exists X\,(|X|\le t\wedge\dots)$ or $\forall X\,(|X|\le t\to\dots)$, for a number term $t$. $\Sigma^B_0=\Pi^B_0$ consists of the formulas with no string quantifiers and only bounded number quantifiers; $\Sigma^B_{i+1}$ ($\Pi^B_{i+1}$) formulas are bounded existential (universal) string quantifiers in front of a $\Pi^B_i$ ($\Sigma^B_i$) formula. A relation definable by both a $\Sigma^B_i$ and a $\Pi^B_i$ formula is $\Delta^B_i$.

**$V^0$.** The axioms of $V^0$ are the twelve basic axioms of $\mathrm{PA}^-$ for $0,1,+,\cdot,\le$, the axioms $X(y)\to y<|X|$ and $y+1=|X|\to X(y)$, string extensionality $(|X|=|Y|\wedge\forall i\le|X|\,(X(i)\leftrightarrow Y(i)))\to X=Y$, and the comprehension scheme

$$
\Sigma^B_0\text{-COMP}:\quad \exists X\le y\ \forall z<y\ \big(X(z)\leftrightarrow\varphi(z)\big)\qquad(\varphi\in\Sigma^B_0).
$$

**$VNC^1$.** $VNC^1$ is $V^0$ together with the axiom $\mathrm{MFV}$, $\exists Y\le 2a+1\ \delta_{\mathrm{MFV}}(a,G,I,Y)$, where

$$
\delta_{\mathrm{MFV}}\equiv\forall x<a\,\Big(\big(Y(x+a)\leftrightarrow I(x)\big)\wedge Y(0)\wedge\Big(0<x\to\Big(Y(x)\leftrightarrow\big(G(x)\wedge Y(2x)\wedge Y(2x+1)\big)\vee\big(\neg G(x)\wedge(Y(2x)\vee Y(2x+1))\big)\Big)\Big)\Big).
$$

Here $G$ encodes a monotone formula as a binary tree ($G(x)$ true when node $x$ is $\wedge$, false when it is $\vee$, with the successors of node $x$ at $2x$ and $2x+1$), $I$ is an assignment to its inputs, and $Y$ is the evaluation, so that the value of the formula is $Y(1)$.

**Predicates for propositional proofs.** Over $V^0$:

- $\mathrm{Fla}(X)$ is a $\Sigma^B_0$-formula saying that the string $X$ codes a propositional formula;
- $Z\vDash X$ is a $\Delta^B_1$-definable relation saying that the truth assignment $Z$ satisfies the formula $X$;
- $\mathrm{Taut}(X)$ is the $\Pi^B_1$-formula $\mathrm{Fla}(X)\wedge\forall Z\le t(|X|)\ Z\vDash X$, where $t$ bounds the number of variables of formulas coded by strings of length $|X|$;
- $\mathrm{Prf}_{F_d}(\Pi,A)$ and $\mathrm{Prf}_F(\Pi,A)$ are $\Sigma^B_0$-definable predicates saying that $\Pi$ is a depth-$d$ Frege proof of $A$ (a Frege proof all of whose formulas have depth at most $d$), respectively a Frege proof of $A$;
- for a propositional proof system $P$, $\mathrm{Prf}_P(\Pi,X)$ is a $\Delta^B_1$-predicate formalizing that $\Pi$ is a $P$-proof of $X$.

Facts recorded in the source: $V^0$ proves the induction scheme for $\Sigma^B_0$-formulas, and $\mathrm{MFV}$ is not provable in $V^0$.

## Expansion

$V^0$ is the theory for $\mathsf{AC}^0$: its $\Sigma^B_1$-definable functions are exactly the $\mathsf{FAC}^0$ functions. Evaluating a monotone formula of size $\ell$ and depth $\lceil\log\ell\rceil$ is $\mathsf{AC}^0$-complete for $\mathsf{NC}^1$, so $\mathrm{MFV}$ raises the strength to $\mathsf{NC}^1$; it fails in $V^0$, since witnessing would put monotone $\mathsf{NC}^1$ in $\mathsf{AC}^0$. Related theories form the chain $V^0\subset V^0(2)\subset VTC^0\subseteq VNC^1\subseteq VL\subseteq\cdots\subseteq VP$, where $V^0(2)$ adds a parity axiom and $VTC^0$ a counting axiom, and their $\Sigma^B_1$-definable functions are exactly $\mathsf{FAC}^0(2)$ and $\mathsf{FTC}^0$.

## Depends on

- [Cook–Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)
- [Frege proof systems](../extended-and-substitution-frege/frege-system.md)

## Proof depends on

None.

## Sources

- Sebastian Müller, "Polylogarithmic cuts in models of V^0", *Logical Methods in Computer Science* 9(1):16, 2013, doi:10.2168/LMCS-9(1:16)2013, arXiv:1303.6075v2 (Section 2: the language $\mathcal L^2_A$, bounded quantifiers and the classes $\Sigma^B_i$, $\Pi^B_i$, $\Delta^B_i$; Section 2.1: depth and bounded-depth Frege; Section 2.2: the axioms of $V^0$ and Fact 2.3; Section 2.3: $VNC^1$, the axiom $\mathrm{MFV}$ and its unprovability in $V^0$; Section 2.4: Definition 2.5 of $\mathrm{Fla}$, $\vDash$, $\mathrm{Taut}$, $\mathrm{Prf}_{F_d}$, $\mathrm{Prf}_F$, and Definition 2.6 for $\mathrm{Prf}_P$).
- Stephen A. Cook and Lila Fontes, "Formal theories for linear algebra", *Logical Methods in Computer Science* 8(1):25, 2012, doi:10.2168/LMCS-8(1:25)2012, arXiv:1101.1449v4 (Section 1: the chain (1.4) of theories; Section 2: Definitions 2.11 and 2.12 of $V^0(2)$ and $VTC^0$, with the statements that the $\Sigma^B_1$-definable functions of $V^0$, $V^0(2)$ and $VTC^0$ are $\mathsf{FAC}^0$, $\mathsf{FAC}^0(2)$ and $\mathsf{FTC}^0$).
