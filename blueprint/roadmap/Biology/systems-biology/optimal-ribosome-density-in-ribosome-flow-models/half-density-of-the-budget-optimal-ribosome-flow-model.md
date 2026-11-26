# Half density of the budget-optimal ribosome flow model

**Ribosome flow model (RFM).** For $n$ sites with occupancies $x_i(t)\in[0,1]$, initiation rate $\lambda_0>0$, elongation rates $\lambda_1,\dots,\lambda_{n-1}>0$ and exit rate $\lambda_n>0$,

$$\dot x_i=\lambda_{i-1}x_{i-1}(1-x_i)-\lambda_ix_i(1-x_{i+1}),\qquad i=1,\dots,n,$$

with the conventions $x_0\equiv1$ and $x_{n+1}\equiv0$. The RFM has a unique globally attracting steady state $e=e(\lambda_0,\dots,\lambda_n)\in(0,1)^n$, and the steady-state translation rate is $R=\lambda_ne_n$.

**Problem 1 with homogeneous budget (Eqs. 11–12).** Maximize $R(\lambda_0,\dots,\lambda_n)$ over $\lambda_0,\dots,\lambda_n\ge0$ subject to $\sum_{i=0}^n\lambda_i\le1$.

**Proposition 4.** The optimal steady-state occupancies $e^*$ satisfy $e_i^*=1-e_{n+1-i}^*$ for $i=1,\dots,n$. They decrease strictly along the chain and cross $1/2$ at the center:
- for even $n$: $e_1^*>\cdots>e_{n/2}^*>\tfrac12>e_{n/2+1}^*>\cdots>e_n^*$;
- for odd $n$: $e_1^*>\cdots>e_{(n-1)/2}^*>e_{(n+1)/2}^*=\tfrac12>\cdots>e_n^*$.

In both cases the optimal mean density is $\rho^*=\tfrac1n\sum_ie_i^*=1/2$. The optimal rates are symmetric, $\lambda_i^*=\lambda_{n-i}^*$, and grow toward the center of the chain.

## Expansion

Under a homogeneous budget, the particle–hole map $x_i\mapsto1-x_{n+1-i}$, together with reversal of the rate vector, maps feasible rate vectors to feasible rate vectors with the same translation rate. Indeed, with $\bar x_i=1-x_{n+1-i}$ and $\bar\lambda_i=\lambda_{n-i}$ the flows satisfy $\bar\lambda_i\bar x_i(1-\bar x_{i+1})=\lambda_{n-i}x_{n-i}(1-x_{n+1-i})$ and the boundary conventions $x_0\equiv1$, $x_{n+1}\equiv0$ are exchanged. Problem 1 has a unique optimal rate vector (it can be cast as a convex program, as shown in earlier work cited by the source), so the optimum is fixed by this symmetry, which gives the antisymmetry $e_i^*=1-e_{n+1-i}^*$ and therefore $\rho^*=1/2$. With general weights $w_i$, numerically solved instances still concentrate near $\rho^*\approx1/2$, although the exact identity no longer holds.

## Sources

- Y. Zarai, M. Margaliot, T. Tuller, "On the ribosomal density that maximizes protein translation rate", PLoS ONE 11 (2016) e0166481. <https://doi.org/10.1371/journal.pone.0166481>, PMCID PMC5115748. Section 2.2, Problem 1, Proposition 4, Eqs. (11)–(15).
