# Applicative similarity and the Howe closure

For closed terms of the lazy untyped lambda calculus with weak-head (lazy) convergence $M \Downarrow \lambda x.M'$, *applicative similarity* $\lesssim$ is the greatest relation such that $M \lesssim N$ and $M \Downarrow \lambda x.M'$ imply $N \Downarrow \lambda x.N'$ with $M'[P/x] \lesssim N'[P/x]$ for every closed $P$; *applicative bisimilarity* is the greatest symmetric such relation. For a relation $R$ on open terms, its *Howe closure* $R^H$ is the least relation such that $x\, R\, N$ implies $x\, R^H\, N$, and $M_i\, R^H\, M_i'$ for the immediate subterms of a term built by a constructor $c$, together with $c(M_1', \dots)\, R\, N$, implies $c(M_1, \dots)\, R^H\, N$. If $R$ is reflexive, $R^H$ is compatible with all term constructors; if $R$ is reflexive and transitive, $R^H$ contains $R$; and if $R$ is moreover closed under substitution (if $M \mathrel{R} N$ in a context extended by $x$, then $M[P/x] \mathrel{R} N[P/x]$ for every term $P$ in that context, as in Pitts, Lemma 5.5.3), $R^H$ is substitutive.

## Expansion

This page becomes ready once these prerequisites are stated:

- Untyped lambda calculus with beta/eta reduction (statement prerequisite; formal statement exists, page pending)

## Sources

- A. M. Pitts, "Howe's method for higher-order languages", in D. Sangiorgi and J. Rutten (eds), *Advanced Topics in Bisimulation and Coinduction*, Cambridge University Press, 2011, Sections 5.5 and 5.9, <https://www.cl.cam.ac.uk/~amp12/papers/howmho/howmho.pdf>
- D. J. Howe, "Proving congruence of bisimulation in functional programming languages", *Information and Computation* 124(2):103–112, 1996
- S. Abramsky, "The lazy lambda calculus", in *Research Topics in Functional Programming*, Addison-Wesley, 1990
