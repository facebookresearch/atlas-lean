# Optimal total density of the ribosome flow model on a ring

**Ribosome flow model on a ring (RFMR).** For $n\ge2$ sites with occupancies $x_i(t)\in[0,1]$ and rates $\lambda_1,\dots,\lambda_n>0$, indices taken modulo $n$ (so $x_0=x_n$, $x_{n+1}=x_1$, $\lambda_0=\lambda_n$),

$$\dot x_i=\lambda_{i-1}x_{i-1}(1-x_i)-\lambda_i x_i(1-x_{i+1}),\qquad i=1,\dots,n.$$

The total density $s=\sum_i x_i$ is conserved; for each $s\in[0,n]$ the RFMR has a unique steady state $e(s)$ with $\sum_i e_i=s$, attracting all solutions on that level set, and the steady-state translation rate is $R(s)=\lambda_ie_i(1-e_{i+1})$ (the same for every $i$).

**Proposition 5 (sign of the slope).** For almost every $s\in[0,n]$,

$$\operatorname{sgn}R'(s)=\operatorname{sgn}\Bigl(\prod_{i=1}^n(1-e_i(s))-\prod_{i=1}^n e_i(s)\Bigr).$$

**Proposition 1 (unique optimal density).** For any rates $\lambda_i>0$ there is a unique $s^*\in(0,n)$ maximizing $R(s)$. With $e^*=e(s^*)$ and $R^*=R(s^*)$,

$$e_1^*\cdots e_n^*=(1-e_1^*)\cdots(1-e_n^*),\qquad (R^*)^n=(\lambda_1\cdots\lambda_n)\,(e_1^*\cdots e_n^*)^2.$$

At the optimum, the product of site occupancies equals the product of site vacancies.

## Expansion

The steady state $e(s)$ is strictly increasing in $s$ (the RFMR is cooperative), so $e_i'(s)>0$ almost everywhere. Differentiating $R=\lambda_ie_i(1-e_{i+1})$ gives $R'=\lambda_i\bigl(e_i'(1-e_{i+1})-e_ie_{i+1}'\bigr)$ for every $i$. If $R'>0$, multiplying the $n$ inequalities $e_i'(1-e_{i+1})>e_ie_{i+1}'$ and cancelling $\prod e_i'$ gives $\prod(1-e_i)>\prod e_i$; conversely that inequality forces $e_\ell'(1-e_{\ell+1})>e_\ell e_{\ell+1}'$ for some $\ell$, hence $R'>0$. The difference of products is positive at $s=0$, negative at $s=n$ and strictly decreasing in $s$, so $R$ increases then decreases with a single maximizer where the products agree. Multiplying $R^*=\lambda_ie_i^*(1-e_{i+1}^*)$ over $i$ and using the equality of products gives the formula for $(R^*)^n$. Proposition 2 of the source gives the sensitivity $(e^*)'$ in closed form.

## Sources

- Y. Zarai, M. Margaliot, T. Tuller, "On the ribosomal density that maximizes protein translation rate", PLoS ONE 11 (2016) e0166481. <https://doi.org/10.1371/journal.pone.0166481>, PMCID PMC5115748. Section 2.1, Propositions 1, 2 and 5, Eqs. (5)–(6).
