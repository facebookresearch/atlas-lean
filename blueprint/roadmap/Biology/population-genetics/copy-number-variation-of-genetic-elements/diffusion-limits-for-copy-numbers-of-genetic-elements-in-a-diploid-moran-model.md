# Diffusion limits for copy numbers of genetic elements in a diploid Moran model

**Model.** A diploid population of constant size $N$ consists of individuals carrying a number of copies of some genetic element (e.g. a transposable element or a duplicated gene). Reproduction events occur at rate $N^2$: individuals $a,b,c$ are chosen, $c$ dies and is replaced by an offspring of $a$ and $b$; a parent with $k$ copies transmits a random number of copies with law $p^N_k$, independently for the two parents. Let $X^N_t\in\mathcal P(\mathbb N_0)$ be the copy-number distribution ($X^N_t(k)$ the fraction of individuals with $k$ copies) and $\Phi(X^N_t)=\sum_jjX^N_t(j)$ the mean copy number. Two inheritance laws are considered: (i) $p^N_k=\mathrm{Bin}(k,\tfrac12+\varepsilon_N)$ with $N\varepsilon_N\to\alpha\in\mathbb R$ (each copy independently transmitted, with a small transmission bias), and (ii) $p^N_k=\mathrm{Unif}\{0,\dots,k\}$ (a uniformly placed breakpoint, each parent transmitting the copies on one side).

**Theorem.** Suppose $\Phi(X^N_0)\to z>0$ in probability and $\sup_N\mathbb E\sum_kk^3X^N_0(k)<\infty$. Then $\Phi(X^N)\Rightarrow Z$ in path space and $X^N\Rightarrow X$ in measure, where:
1. in case (i), $dZ=\alpha Z\,dt+\sqrt Z\,dW$ (a Feller branching diffusion with drift $\alpha$) and $X_t=\mathrm{Poi}(Z_t)$;
2. in case (ii), $dZ=\sqrt{Z(Z+2)}\,dW$ and $X_t=\mathrm{NB}\big(2,\tfrac2{2+Z_t}\big)$, the negative binomial law with $2$ successes and mean $Z_t$.

The diffusion coefficient of $Z$ is the variance of the quasi-equilibrium copy-number law ($z$ for the Poisson, $z(z+2)$ for the negative binomial). By contrast, if a parent transmits either none or all of its copies with probability $\tfrac12$ each, the fraction of individuals with no copies tends to one, so all copies are lost in the limit even though the mean transmission is unbiased.

## Expansion

The general result behind the theorem concerns Markov processes $X^N$ with a strong drift towards a subspace $D$ along which a function $\Phi$ evolves slowly: if the fast dynamics, for each fixed value of $\Phi$, relax to a unique point $\Xi(\Phi)$ of $D$, then $\Phi(X^N)$ converges to the solution of the martingale problem with generator $(G_0(g\circ\Phi))\circ\Xi$, and $X^N$ converges in measure to $\Xi(Z)$ (an infinite-dimensional version of Katzenberger's averaging). Here, mixing of copies by reproduction is fast (rate $N^2$ per individual), so the copy-number distribution is pushed to a one-parameter family indexed by its mean: under binomial thinning it is Poisson, because halving-thinning a Poisson($z$) number of copies gives Poisson($z/2$), and the sum of the contributions of two independent parents is again Poisson($z$), and under uniform breakpoints it is negative binomial. The mean itself changes only through resampling noise and the transmission bias, on the slower time scale.

## Sources

- S. A. Adeosun, P. Pfaffelhuber, "Markov processes forced on a subspace by a large drift, with applications to population genetics", arXiv:2602.16342 (2026), Section 2 (the abstract limit theorem for processes forced on a subspace) and Section 3 (copy-number model, jump rates, the limit theorem for cases (i) and (ii), and the remarks on general inheritance laws), <https://doi.org/10.48550/arXiv.2602.16342>.
