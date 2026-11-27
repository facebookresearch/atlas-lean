# Conditioning versus mechanistic knockout in dynamic Bayesian gene networks

**Setting.** Expression levels $X_{ik}$ of genes $i=1,\dots,N$ at times $t_1<\dots<t_K$ follow a *mechanistic* model if

$$X_{ik} = F_{ik}\big(X_{1,[1,k-1]},\dots,X_{N,[1,k-1]};\,U_{ik}\big), \qquad 2\le k\le K,$$

with independent noises $U_{ik}$, independent of the initial expressions; dynamic Bayesian networks are mechanistic. A knockout of gene $1$ can be predicted in two ways: the *conditional* model $X^{\mathrm{cond}}$ conditions the fitted law on $X_{1k}=0$ for all $k$, while the *mechanistic* model $X^{\mathrm{meca}}$ replaces $F_{1k}$ by $0$ and propagates the change through the other $F_{ik}$. Let $G'$ be the static gene network with gene $1$ and its edges removed; a connected component $\mathcal{C}$ of $G'$ is *downstream* of gene $1$ if no edge goes from any $j\in\mathcal{C}$ to gene $1$, and *upstream* if no edge goes from gene $1$ to $\mathcal{C}$ (by acyclicity, every component is one or the other).

**Theorem.**

1. For a component $\mathcal{C}$ downstream of gene $1$, $(X^{\mathrm{cond}}_{ik})_{i\in\mathcal{C},k}$ and $(X^{\mathrm{meca}}_{ik})_{i\in\mathcal{C},k}$ have the same law, namely that of $(X_{ik})_{i\in\mathcal{C},k}$ conditioned on $X_{1k}=0$ for all $k$, and each is independent of the remaining genes $\{2,\dots,N\}\setminus\mathcal{C}$.
2. For a component $\mathcal{C}$ upstream of gene $1$, $(X^{\mathrm{meca}}_{ik})_{i\in\mathcal{C},k}$ has the same law as the unperturbed $(X_{ik})_{i\in\mathcal{C},k}$ and is independent of the other genes, whereas conditioning generally biases the upstream genes.
3. In the linear Gaussian case the unperturbed law is $\mathcal{N}(H^{-1}\mu, H^{-1}\Lambda H^{-\top})$ for the matrix $H$ of the linear recursion, mean input $\mu$ and noise covariance $\Lambda$, and both alteration models are again Gaussian with explicit parameters.

## Expansion

A mechanistic knockout is a do-intervention on gene $1$: it cuts the arrows into gene $1$ but leaves the generating mechanisms of all other genes intact, so genes that do not depend on gene $1$ keep their law. Conditioning on $X_{1\cdot}=0$ instead updates beliefs about the causes of gene $1$, which shifts upstream genes; for downstream genes, whose only link to gene $1$ is through its value, the two coincide.

## Sources

- N. Champagnat, R. Loubaton, L. Vallat, P. Vallois, "Modelling the effects of biological intervention in a dynamical gene network", *Journal of Mathematical Biology* 93(3) (2026), 44, Section 3 (mechanistic models) and Propositions 4.2–4.3, Theorem 4.4, <https://doi.org/10.1007/s00285-026-02458-3> (preprint arXiv:2505.04266).
