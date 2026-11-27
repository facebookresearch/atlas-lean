# Jacobian criterion reduces to orientations of square embedded networks

**Setting.** Consider a chemical reaction network with mass-action kinetics. A *CFSTR network* contains the outflow reaction $X_i \to 0$ for every species. Its *Jacobian determinant* $\mathrm{Jac}(\mathcal{N})$ is the determinant of the negative Jacobian of the mass-action system, a polynomial in the concentrations $x_i$ and rate constants $\kappa_j$. The network *passes the Jacobian criterion* if every term of this polynomial has positive coefficient; by Craciun and Feinberg, a CFSTR that passes cannot be multistationary (have two positive steady states for any rate constants).

For a *square* network with $n$ species and $n$ reactions $y_i \to y_i'$, let $M_N$ be the reactant matrix (rows $y_i$) and $R_N$ the reaction matrix (rows $y_i - y_i'$), and define the *orientation* $\mathrm{Or}(N) = \operatorname{sign}\big(\det M_N \det R_N\big) \in \{-1,0,1\}$. A *$k$-square embedded network* of $\mathcal{N}$ is obtained by choosing $k$ species and $k$ non-flow reactions involving all of them and deleting all other species from those reactions.

**Theorem.** For a CFSTR $\mathcal{N}$ with non-flow subnetwork $G$, the following are equivalent:
1. $\mathcal{N}$ passes the Jacobian criterion;
2. every square embedded network of $G$ has nonnegative orientation;
3. $G$ has no self-catalyzing reaction, and every square embedded network of $G$ that has no inflows, outflows, generalized inflows $0 \to \sum a_iX_i$ or generalized outflows $aX_i \to bX_i$ ($0 \le b \le a$), and in which each species occurs in at least two reactions, has nonnegative orientation.

Moreover one may first delete inflows, outflows, generalized inflows, one-species reactions $aX_i \to bX_i$ with $b < a$, non-reactant species, and species occurring in exactly one reaction (unless self-catalytic) without changing the outcome.

**Theorem (total molecularity two).** If every species has total molecularity $\mathrm{TM}(X_i) = \sum_j (y_{ji} + y'_{ji}) \le 2$ (summing over non-flow reactions, a reversible pair counted once), then the CFSTR passes the Jacobian criterion and has no multiple steady states. The same conclusion holds for every weakly reversible network whose species all have total molecularity at most two.

## Expansion

By the Cauchy–Binet expansion, the coefficient of each monomial in $\mathrm{Jac}(\mathcal{N})$ is a sum of products $\det M_N\det R_N$ over square embedded networks, and outflows contribute diagonal identity blocks; so all coefficients are positive exactly when no embedded square network has negative orientation. Pivots in $M_N$ or $R_N$ (rows or columns with a single nonzero entry) let one expand the determinants and delete the corresponding species and reaction, which justifies the reduction steps; a self-catalyzing reaction alone already gives a negative $1$-square orientation. When each species appears with total multiplicity at most two, the surviving square networks are cycles whose orientation can be computed directly and is never negative.

## Sources

- Badal Joshi and Anne Shiu, "Simplifying the Jacobian Criterion for Precluding Multistationarity in Chemical Reaction Networks", SIAM Journal on Applied Mathematics 72 (2012), 857–876, <https://doi.org/10.1137/110837206>; numbering as in arXiv:1106.1578: Definitions 2.2, 2.6 and 4.6, Proposition 4.7, Theorems 4.9 and 4.11, Corollary 4.10, Theorem 5.1 and Corollary 5.2.
