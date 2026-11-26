# Turing-like instability of sequential double phosphorylation

**Network.** Sequential, distributive phosphorylation of a substrate at two sites by a kinase $K$ and dephosphorylation by a phosphatase $F$, with mass-action kinetics:
$$S_0+K\underset{k_2}{\overset{k_1}{\rightleftharpoons}}S_0K\xrightarrow{k_3}S_1+K\underset{k_5}{\overset{k_4}{\rightleftharpoons}}S_1K\xrightarrow{k_6}S_2+K,$$
$$S_2+F\underset{k_8}{\overset{k_7}{\rightleftharpoons}}S_2F\xrightarrow{k_9}S_1+F\underset{k_{11}}{\overset{k_{10}}{\rightleftharpoons}}S_1F\xrightarrow{k_{12}}S_0+F.$$
Order the nine species as $c=([S_0],[K],[S_0K],[S_1],[S_1K],[S_2],[F],[S_2F],[S_1F])$ with diffusion coefficients $d_1,\dots,d_9>0$. The stoichiometric matrix has rank $6$ (three conserved totals), and the positive steady states admit a monomial parameterization $\bar c(\xi)$ in three free parameters $\xi_1,\xi_2,\xi_3>0$.

**Statement (Lemma 3.8).** Suppose the catalytic constants and the diffusion coefficients of the four enzyme-substrate complexes satisfy
$$\frac{k_3k_9}{k_6k_{12}}<\frac{d_3d_8}{d_5d_9}.$$
Fix $\xi_2,\xi_3>0$. Then the constant coefficient $a_6(\xi_1)$ of $\det(J(\bar c)D^{-1}-\mu I)=\mu^3(a_0\mu^6+\cdots+a_6)$ has a unique positive zero $\bar\xi_1$, and for every $\xi_1>\bar\xi_1$ the steady state $\bar c(\xi)$ satisfies the coefficient-sign conditions; hence on any domain meeting the size thresholds there is a Neumann eigenvalue $\mu_\ell$ for which $J(\bar c)-\mu_\ell D$ has an odd number (at least one) of positive eigenvalues. If $\bar c$ is in addition stable for the well-mixed ODE, it undergoes a Turing-like instability.

## Depends on

- [Coefficient-sign criterion for Turing-like instability with conservation laws](coefficient-sign-criterion-for-turing-like-instability.md)

## Expansion

Symbolic computation at the monomial parameterization shows: every term of the numerator of $a_0$ is negative, so $\operatorname{sign}a_0=-1=(-1)^9$ always; the numerator of $a_6$ is a quadratic in $\xi_1$, $(d_3d_8k_{12}k_6-d_5d_9k_3k_9)\gamma_0\xi_1^2+\gamma_1\xi_1+\gamma_2$, with $\gamma_0>0$ and $\gamma_2<0$; the common denominator is positive. Under the stated inequality the leading coefficient is positive and the constant term negative, so $a_6(\xi_1)$ changes sign exactly once, at $\bar\xi_1$, and $a_6>0=(-1)^{10}$ for $\xi_1>\bar\xi_1$. The criterion then applies. Numerical continuation in one and two dimensions confirms bifurcating patterned branches. The condition says the substrate-enzyme complexes formed in the second phosphorylation and first dephosphorylation steps must diffuse sufficiently fast relative to the others, weighted by the catalytic rates.

## Sources

- Carsten Conradi, Maya Mincheva, Hannes Uecker, "Conditions for spatial instabilities and pattern formation from monomial steady state parameterizations", arXiv:2605.16049 (2026), Section 2 (network and monomial parameterization), Section 3.3 (Facts 1-6) and Lemma 3.8, <https://doi.org/10.48550/arXiv.2605.16049>
