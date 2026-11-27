# Equational derivability is replacement of equals

For every set $E$ of equations and all terms $s, t$: $s \leftrightarrow_E^* t$ if and only if $E \vdash s \approx t$ is derivable in the [equational calculus](equational-calculus.md).

**Proof.** If $s \leftrightarrow_E t$, then $E \vdash s \approx t$ by induction on the depth of the position at which the equation is applied, using Instance, Congruence and Symmetry; chains follow by Reflexivity and Transitivity. Conversely, induct on the size of the derivation.

## Depends on

- [Equational calculus](equational-calculus.md)
- [Equational consequence and E-algebras](equational-consequence-and-e-algebras.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.2, Lemma 4.2 with its proof, p. 108.
