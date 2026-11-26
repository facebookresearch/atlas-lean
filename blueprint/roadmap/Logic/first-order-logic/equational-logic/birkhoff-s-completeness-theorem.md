# Birkhoff's completeness theorem for equational logic

Let $X$ be a countably infinite set of variables and $E$ a set of universally quantified equations. For all terms $s, t \in T_\Sigma(X)$ the following are equivalent:

1. $s \leftrightarrow_E^* t$;
2. $E \vdash s \approx t$ is derivable in the [equational calculus](equational-calculus.md);
3. $s \approx_E t$, that is, $E \models \forall \vec x\,(s \approx t)$;
4. $T_\Sigma(X)/E \models \forall \vec x\,(s \approx t)$.

**Proof.** (1) ⇔ (2) is replacement of equals. (2) ⇒ (3) by induction on the derivation. (3) ⇒ (4) because $T_\Sigma(X)/E$ is an $E$-algebra. For (4) ⇒ (2), rename the variables of the equation into $X$, which is possible as $X$ is countably infinite, and evaluate under the assignment $x_i \mapsto [x_i]$, under which every term $u$ denotes $[u]$; then $[s] = [t]$.

## Depends on

- [Equational calculus](equational-calculus.md)
- [Equational consequence and E-algebras](equational-consequence-and-e-algebras.md)
- [The term algebra modulo E is an E-algebra](term-algebra-modulo-an-equational-theory.md)

## Proof depends on

- [Equational derivability is replacement of equals](equational-derivability-is-replacement-of-equals.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.2, Lemma 4.5 and Theorem 4.6 ("Birkhoff's Theorem") with their proofs, p. 109.
