# Poisson equilibrium of Muller's ratchet with compensatory mutations

**Model.** In a large asexual population the type of an individual is its number $k\in\mathbb N_0$ of deleterious mutations, and type $k$ has fitness reduced by $\alpha k$ ($\alpha\ge0$). Along lines of descent new mutations arise at rate $\lambda\ge0$ and each present mutation is removed by a compensatory mutation at rate $\gamma\ge0$. The type frequencies $\underline X=(X_k)_{k\ge0}$ in the simplex $\mathbb S=\{\underline x\in\mathbb R_+^{\mathbb N_0}:\sum_kx_k=1\}$ follow the Fleming–Viot system

$$dX_k=\Bigl(\alpha\Bigl(\sum_{\ell}(\ell-k)X_\ell\Bigr)X_k+\lambda(X_{k-1}-X_k)+\gamma\bigl((k+1)X_{k+1}-kX_k\bigr)\Bigr)dt+\sum_{\ell\ne k}\sqrt{\tfrac1NX_kX_\ell}\,dW_{k\ell},$$

with $X_{-1}=0$, independent Brownian motions $W_{k\ell}=-W_{\ell k}$, and population size parameter $N$. The case $\gamma=0$ is the Fleming–Viot version of Muller's ratchet. Let $\mathbb S_\xi=\{\underline x\in\mathbb S:\sum_kx_ke^{\xi k}<\infty\}$.

**Theorem (well-posedness).** For $\underline x\in\mathbb S_\xi$, $\xi>0$, $N\in(0,\infty)$ and $\alpha,\lambda,\gamma\ge0$, the system has a unique weak solution started at $\underline x$, with continuous paths in $\mathbb S_\xi$.

**Theorem (infinite-population limit).** For $N=\infty$ (no noise) the system has a unique solution in $\mathbb S_\xi$. With $c=\alpha+\gamma$, $a_t=\gamma(1-e^{-ct})/c$, $b_t=e^{-ct}$ and $\ell_t=\lambda(1-e^{-ct})/c$, it is

$$x_k(t)=\frac{\sum_{i\ge0}x_i(0)\sum_{j=0}^{i\wedge k}\binom ij\,a_t^{\,i-j}\,b_t^{\,j}\,\dfrac{\ell_t^{\,k-j}}{(k-j)!}}{\sum_{i\ge0}x_i(0)\,(a_t+b_t)^i\,e^{\ell_t}},$$

where the denominator is the sum over $k$ of the numerators. If $\gamma>0$ or $x_0(0)>0$, then

$$x_k(t)\xrightarrow[t\to\infty]{}e^{-\lambda/(\alpha+\gamma)}\,\frac{1}{k!}\Bigl(\frac{\lambda}{\alpha+\gamma}\Bigr)^k,\qquad k=0,1,2,\dots,$$

so for $\gamma>0$ the unique equilibrium is the Poisson distribution with mean $\lambda/(\alpha+\gamma)$: compensatory mutations stop the deterministic ratchet from losing its best class.

## Depends on

- [Muller's ratchet model and almost sure clicking](../muller-s-ratchet-model-and-almost-sure-clicking.md)

## Expansion

Well-posedness is proved for the martingale problem on $\mathbb S_\xi$ using bounds on exponential moments $h_\xi(\underline X)=\sum_kX_ke^{\xi k}$ (selection against high types keeps them finite) and a Girsanov change of measure that removes the selection term, reducing uniqueness to the neutral mutation–compensation system. For the deterministic system, consider a particle system in which each individual carries mutations that are added at rate $\lambda$, removed independently at rate $\gamma$, and in which an individual with $k$ mutations is killed at rate $\alpha k$; conditioning on survival gives exactly the normalized equation. Each initial mutation independently survives (neither compensated nor causing a kill) with probability $b_t$ and is compensated with probability $a_t$, which accounts for the binomial term, while newly arisen surviving mutations form a Poisson number with mean $\ell_t$. The cumulant generating function of $\underline x(t)$ satisfies a linear first-order PDE, which provides the closed form and a duality. As $t\to\infty$, $b_t\to0$, $a_t\to\gamma/c$ and $\ell_t\to\lambda/c$; when $\gamma>0$ (or the best class is initially present) the normalization stays positive and the initial condition is forgotten.

## Sources

- P. Pfaffelhuber, P. R. Staab, A. Wakolbinger, "Muller's ratchet with compensatory mutations", *The Annals of Applied Probability* 22 (2012), 2108–2132, <https://doi.org/10.1214/11-AAP836>; preprint arXiv:1108.4059, <https://doi.org/10.48550/arXiv.1108.4059>. Numbering of the arXiv version: Section 1 (system $(\ast)$, Theorems 1 and 2), Section 4 (Proposition 4.1, Lemma 4.2, Proposition 4.4), Section 5 (Propositions 5.1 and 5.2, Corollary 5.3).
