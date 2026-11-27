# λΔ-terms are classical proofs

For the implicational fragment of classical propositional logic and the simply typed [λΔ-calculus](the-lambda-delta-calculus.md):

1. if $\Gamma \vdash M : \varphi$, then $|\Gamma| \vdash \varphi$ classically, where $|\Gamma| = \{\varphi : (x : \varphi) \in \Gamma\}$;
2. if $\Gamma \vdash \varphi$ classically, then $\Gamma' \vdash M : \varphi$ for some term $M$, where $\Gamma' = \{x_\varphi : \varphi : \varphi \in \Gamma\}$.

## Depends on

- [The λΔ-calculus](the-lambda-delta-calculus.md)

## Expansion

This page becomes ready once:

- Natural deduction for classical implicational propositional logic with $\bot$, with its provability relation $\Gamma \vdash \varphi$ (statement prerequisite; not yet stated)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Section 8.1, Definition 8.1.2 and Proposition 8.1.3 (classical implicational logic, with double-negation elimination), and Proposition 8.3.4.
