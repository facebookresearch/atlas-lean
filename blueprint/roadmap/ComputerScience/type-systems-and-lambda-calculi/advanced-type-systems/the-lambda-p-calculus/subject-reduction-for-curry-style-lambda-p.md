# Subject reduction for Curry-style λP

For a pure λ-term $N$ write $\Gamma \vdash_P N : \tau$ if $N$ is the type erasure $|M|$ of a term $M$ with $\Gamma \vdash M : \tau$ in [λP](the-calculus-lambda-p.md), in its presentation without λ-abstractions in constructors. Curry-style λP has the
subject-reduction property: if $\Gamma \vdash_P N : \tau$ and $N \twoheadrightarrow_\beta N'$, then $\Gamma \vdash_P N' : \tau$.

## Depends on

- [The calculus λP](the-calculus-lambda-p.md)
- [β-reduction](../../untyped-lambda-calculus/beta-reduction-and-confluence/beta-reduction.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Section 10.4, Definition 10.4.1 and Proposition 10.4.2, whose proof the notes leave to their reference [5], S. van Bakel, L. Liquori, S. Ronchi della Rocca and P. Urzyczyn, "Comparing cubes of typed and type assignment systems", *Annals of Pure and Applied Logic* 86:267–303, 1997.
