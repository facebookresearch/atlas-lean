# Counting axioms modulo $m$

The counting axiom $\mathrm{Count}^V_m$ says that a set $V$ of size $N\not\equiv0\pmod m$ cannot be partitioned into blocks of size $m$. Constant-depth Frege with counting axioms modulo $m$ adds all substitution instances of these formulas as axioms.

For a set $S$ let $[S]^m=\{e\subseteq S: |e|=m\}$, and for $e,f\in[S]^m$ write $e\perp f$ ($e$ *conflicts with* $f$) if $e\ne f$ and $e\cap f\ne\emptyset$. Let $m>1$, let $N\not\equiv0\pmod m$, and let $V$ be a set of $N$ elements, with a variable $x_e$ for each $e\in[V]^m$. The counting formula is

$$
\mathrm{Count}^V_m=\bigvee_{v\in V}\Bigl(\bigwedge_{e\in[V]^m,\ e\ni v}\neg x_e\Bigr)\ \vee\bigvee_{e,f\in[V]^m,\ e\perp f}(x_e\wedge x_f).
$$

It is a tautology: if the true variables $x_e$ formed pairwise disjoint blocks covering every point of $V$, they would partition $V$ into blocks of size $m$, which is impossible since $m\nmid N$. *Frege with counting modulo $m$* derivations are Frege derivations that may also use substitution instances of $\mathrm{Count}^{[N]}_m$, for any $N\not\equiv0\pmod m$, as axioms; the constant-depth version bounds the depth of all formulas as in [bounded-depth Frege](../bounded-depth-frege-systems/bounded-depth-frege-proofs.md).

## Expansion

Counting axioms let bounded-depth Frege reason about parity and other modular counts, which it cannot do on its own: lower bounds for constant-depth Frege with counting axioms were proved by converting small proofs into low-degree Nullstellensatz refutations. Conversely, these systems [polynomially simulate Nullstellensatz refutations modulo $m$](counting-axioms-simulate-nullstellensatz.md), and they [refute inconsistent sparse linear systems modulo a prime $q$ in polynomial size](counting-axioms-refute-sparse-linear-systems.md). A related but different extension adds modular counting *connectives*, giving [AC$^0[p]$-Frege](../bounded-depth-frege-systems/ac0p-frege-systems.md).

## Depends on

- [Bounded-depth Frege proofs](../bounded-depth-frege-systems/bounded-depth-frege-proofs.md)

## Proof depends on

None.

## Sources

- Russell Impagliazzo and Nathan Segerlind, "Constant-Depth Frege Systems with Counting Axioms Polynomially Simulate Nullstellensatz Refutations", *ACM Transactions on Computational Logic* 7(2), 2006, https://doi.org/10.1145/1131313.1131314; numbering as in arXiv:cs/0308012v1 (Section 2, definitions of [S]^m and conflicting sets; Section 2.1.2, definition of Count^V_m).
