# Bounded-depth Frege proofs

A bounded-depth (AC$^0$-) Frege proof is a Frege proof whose formulas have depth at most a fixed constant $d$, depth counting alternations of unbounded fan-in AND and OR. A tautology family has polynomial-size bounded-depth Frege proofs when one depth bound and one polynomial size bound serve every member.

**Depth.** For a formula $\varphi$ over $\wedge,\vee,\neg$, the *logical depth* $\mathrm{ldp}(\varphi)$ is the depth of $\varphi$ as a binary tree, and the *depth* $\mathrm{dp}(\varphi)$ is the maximum number of alternations between AND and OR connectives on a root-to-leaf path, not counting negations, plus one. For example $(A\wedge B)\wedge C$ has logical depth $2$ and depth $1$, and every CNF or DNF has depth $2$.

**Cut-depth formulation.** Work in the propositional sequent calculus PK, whose lines are sequents $A_1,\dots,A_k\longrightarrow B_1,\dots,B_m$, with the axiom $A\longrightarrow A$, the structural rules, the left and right introduction rules for each connective and the cut rule. An $\mathrm{AC}^0_k$-*Frege proof* (cut-depth $k$ proof) is a PK proof in which every cut formula has depth at most $k$; other formulas may be arbitrary. This agrees with the definition requiring all formulas to have depth at most $k$ whenever the proven formula has depth at most $k$. A proof is *tree-like* if each sequent is used at most once, and its *size* is the sum of the sizes of all formulas in it.

**Refutation formulation.** Equivalently, take the connectives $\neg$ and unbounded fan-in $\bigvee$ with the axiom scheme $A\vee\neg A$ and the rules weakening ($A$ gives $A\vee B$), cut ($A\vee B$ and $\neg A\vee C$ give $B\vee C$), merging ($\bigvee X\vee\bigvee Y$ gives $\bigvee(X\cup Y)$) and unmerging (the converse). A refutation of a set $\mathcal H$ of formulas is a derivation from $\mathcal H$ ending in FALSE, and its size is the number of symbols in it. A family of tautologies $\tau_n$ of sizes $s(n)$ has *polynomial-size constant-depth Frege proofs* if there are constants $c$ and $d$ such that every $\tau_n$ has a proof in which every formula has depth at most $d$ and whose size is $O(s(n)^c)$.

By Cook and Reckhow, any two Frege systems simulate each other with a polynomial increase in size and a linear increase in depth, so the class of families with polynomial-size constant-depth proofs does not depend on the chosen Frege system.

## Expansion

Under the informal correspondence between proof systems and circuit classes, the lines of polynomial-size bounded-depth Frege proofs are non-uniform $\mathrm{AC}^0$ functions, just as resolution lines are clauses and Frege lines are $\mathrm{NC}^1$ formulas. This is why random-restriction methods for $\mathrm{AC}^0$ circuits, such as [Håstad's switching lemma](../../../../TheoryOfComputation/circuit-complexity/lower-bounds-for-ac0-circuits/hastad-s-switching-lemma.md), are the standard source of lower bounds for these systems. Extending the connectives by modular counting gates gives [AC$^0[p]$-Frege](ac0p-frege-systems.md), and replacing them by threshold gates gives [TC$^0$-Frege](tc0-frege-systems.md).

## Depends on

- [Cook–Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Proof depends on

None.

## Sources

- Yuval Filmus, Toniann Pitassi and Rahul Santhanam, "Exponential Lower Bounds for AC0-Frege Imply Superpolynomial Frege Lower Bounds", *Automata, Languages and Programming (ICALP 2011), Part I*, Lecture Notes in Computer Science 6755, pp. 618-629, 2011, https://doi.org/10.1007/978-3-642-22006-7_52 (Section 2, definitions of logical depth, depth and AC0_k-Frege proofs).
- Russell Impagliazzo and Nathan Segerlind, "Constant-Depth Frege Systems with Counting Axioms Polynomially Simulate Nullstellensatz Refutations", *ACM Transactions on Computational Logic* 7(2), 2006, https://doi.org/10.1145/1131313.1131314; numbering as in arXiv:cs/0308012v1 (Section 2.1.1, constant-depth Frege systems).
