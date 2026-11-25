# Range criterion for a core of a semigroup generator

Let $A$ be the generator of a [strongly continuous contraction semigroup](strongly-continuous-contraction-semigroups.md) on a real Banach space $L$, and let $D\subseteq\mathcal D(A)$ be a subspace. Then $D$ is a core for $A$ if and only if $D$ is dense in $L$ and the range $\{\lambda f-Af:f\in D\}$ is dense in $L$ for some $\lambda>0$.

## Depends on

- [Strongly continuous contraction semigroups, generators and cores](strongly-continuous-contraction-semigroups.md)

## Expansion

A proof page must use that $A$ is closed and that $\lambda-A:\mathcal D(A)\to L$ is a bijection with $\lVert(\lambda-A)^{-1}\rVert\le1/\lambda$ for $\lambda>0$; for the converse direction, approximate $g=(\lambda-A)f$ by $(\lambda-A)f_n$ with $f_n\in D$, deduce $f_n\to f$ and $Af_n\to Af$ from the resolvent bound, so that $f$ lies in the domain of the closure of $A|_D$ with the same value; and for the direct direction, show that density of the range passes from $\mathcal D(A)$, where the range is all of $L$, to a core.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, <https://doi.org/10.1002/9780470316658>, Chapter 1, Section 3.
