# Expectations of factorized functions as evidence probabilities in a Bayesian network

**Setting.** Let $X=(X_v)_{v\in V}$ be discrete random variables whose joint law is a Bayesian network, and let $h(x)=\prod_{B\in\mathcal B}h_B(x_B)$ for a family $\mathcal B$ of subsets of $V$ and nonnegative functions $h_B$. For each $B\in\mathcal B$ pick a constant $k_B\ge\max_{x_B}h_B(x_B)$, for example the maximum itself, and add a binary child $Y^B$ of the nodes $X_B$ with

$$
P(Y^B=1\mid X=x)=P(Y^B=1\mid X_B=x_B)=h_B(x_B)/k_B ,
$$

the $Y^B$ being conditionally independent given $X$. Adding children creates no directed cycle, so the extended network represents the joint law of $(X,Y)$.

**Proposition (expectation as probability).** For every $\mathcal B'\subseteq\mathcal B$,

$$
E\Big[\prod_{B\in\mathcal B'}h_B(X_B)\Big]=P\Big(\bigcap_{B\in\mathcal B'}\{Y^B=1\}\Big)\prod_{B\in\mathcal B'}k_B .
$$

**Proposition (normalizing-constant ratio).** In a junction-tree representation with charge $g$ and normalizing constant $N_1=\sum_xg(x)$, enter likelihood evidence $\ell_B(1)=k_B$, $\ell_B(0)=0$ on each $Y^B$, $B\in\mathcal B'$, and let $N_2$ be the normalizing constant after propagation. Then

$$
E\Big[\prod_{B\in\mathcal B'}h_B(X_B)\Big]=\frac{N_2}{N_1}.
$$

Thus the expectation of any product of factors, such as a likelihood averaged over unobserved genotypes, comes out of a single round of probability propagation, at a cost governed by the clique sizes of the triangulated extended network.

## Depends on

- [Bayesian network](../../../../../ComputerScience/machine-learning/probabilistic-graphical-models/bayesian-networks/bayes-net.md)

## Expansion

The first identity is the tower property: $E[\prod_Bh_B(X_B)]=E[\prod_Bk_BP(Y^B=1\mid X)]$, and conditional independence turns the product of conditional probabilities into $P(\bigcap_B\{Y^B=1\}\mid X)$. For the second, entering likelihood evidence $\ell$ multiplies the charge by $\prod\ell$, so $N_2/N_1=E[\prod_B\ell_B(Y^B)]=E[\prod_Bk_B\mathbf 1\{Y^B=1\}]$, which is the right side of the first identity. Each parent set $X_B$ becomes a complete set after moralization, so it lies in some clique, and the evidence can be absorbed locally.

## Sources

- T. Graversen, S. Lauritzen, "Computational aspects of DNA mixture analysis", *Statistics and Computing* 25 (2015), 527–541, <https://doi.org/10.1007/s11222-014-9451-7>; preprint arXiv:1307.4956 (2013), Section 3.1 (computation by auxiliary variables, Propositions 1 and 2), <https://doi.org/10.48550/arXiv.1307.4956>.
