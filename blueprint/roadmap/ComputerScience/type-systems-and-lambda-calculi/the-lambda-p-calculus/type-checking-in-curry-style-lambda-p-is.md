# Type checking in Curry-style λP is undecidable

For the Curry-style variant of [λP](the-calculus-lambda-p.md), with $\Gamma \vdash_P N : \tau$ meaning that the pure term $N$ is the erasure of a λP term of type $\tau$ in
$\Gamma$, it is undecidable, given $\Gamma$, $N$ and $\tau$, whether $\Gamma \vdash_P N : \tau$ (Dowek). This contrasts with type reconstruction, which is decidable in
polynomial time because the typable pure terms are exactly the [simply typable ones](curry-style-lambda-p-types-exactly-the-simply.md).

## Depends on

- [The calculus λP](the-calculus-lambda-p.md)

## Expansion

This page becomes ready once:

- G. Dowek, "The undecidability of typability in the lambda-pi-calculus", *Typed Lambda Calculi and Applications*, LNCS 664, pages 139–145, 1993, as listed in the bibliography of the lecture notes below, checked for the statement and its proof, which the lecture notes below cite without proof (source check)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Definition 10.4.1 and Theorem 10.4.6 (Dowek), stated without proof.
