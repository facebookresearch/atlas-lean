# Posterior tail bounds for divergence time under context-dependent evolution

**Setting.** Sequences $\mathbf x\in\mathcal A^n$ over a finite alphabet evolve by a time-homogeneous continuous-time Markov chain with **context-dependent** (dependent-site) rates: site $i$ mutates from $x_i$ to $b$ at rate $\gamma_i(b;\tilde x_i)$, where $\tilde x_i=(x_i,x_{c(i,1)},\dots,x_{c(i,k)})$ collects the states of $k$ context sites (for example neighbouring bases, as in CpG hypermutability); $k=0$ is the independent-site case. Only single-site substitutions occur, each site has exactly $q$ reachable states in every context, and all nonzero rates lie in $[\gamma_{\min},\gamma_{\max}]$ with $0<\gamma_{\min}\le\gamma_{\max}<\infty$; $\lambda\ge\gamma_{\max}$ is a uniformization rate. Given two aligned sequences $\mathbf x,\mathbf y$, with $\mathbf y$ obtained from $\mathbf x$ by running the chain for time $T$, place a prior with density $\eta_0$ on $T$ and let $\eta(\cdot\mid\mathbf x,\mathbf y)$ be the posterior. Let $r=d_H(\mathbf x,\mathbf y)$ be the Hamming distance and $\hat p=r/n$ the $p$-distance; write $J=[a\,r/n,\,b\,r/n]$ for fixed $0<a<b$ and $\eta_0(J)$ for its prior mass.

**Theorem 1 (general context dependence).** There are constants $c_1\in(0,1)$ and $c_0,c_2,c_3\in(0,\infty)$, depending on $\gamma_{\min},\gamma_{\max},\lambda,q,a,b$, such that for all large $n$ and all $\mathbf x,\mathbf y$ with $c_0\le r\le c_1n/\log n$,

$$\eta\bigl(T>c_3\,\hat p\log n\mid\mathbf x,\mathbf y\bigr)\le\frac{e^{-c_2r\log n}}{\eta_0(J)}.$$

If $\eta_0(t)\ge Ct^\alpha$ near $0$, then $\eta_0(J)=\Omega(n^{-(\alpha+1)})$ and the bound decays faster than any polynomial in $n$ as soon as $r\to\infty$.

**Theorem 2 (symmetric models).** If all nonzero rates equal a common $\gamma$, there are constants $c_0'\in(0,1)$ and $c_1',c_2'>0$ such that, whenever $r\le c_0'n$ and $r/\log n\to\infty$,

$$\eta\bigl(T>c_2'\,\hat p\mid\mathbf x,\mathbf y\bigr)\le\frac{e^{-c_1'r}}{\eta_0(J)},$$

so the posterior concentrates on times of the order of the $p$-distance, without the $\log n$ factor.

## Expansion

Dependent-site models have no closed-form likelihood, but uniformization at rate $\lambda$ writes it as a Poisson mixture over the number of potential substitution events. The posterior tail is bounded by comparing the likelihood at large $t$ with its value on the interval $J$ near the $p$-distance: a large $t$ needs many events (a Poisson tail term) whose net effect nonetheless leaves only $r$ differences. A coupling of the sequence chain with a chain on the set of differing sites controls this, using hitting times and canonical-path bounds on mixing; context dependence can make some differences sticky, which costs the extra $\log n$ factor. In the symmetric case the difference process is itself Markov and reversible, giving the sharper bound. The results justify importance-sampling or MCMC schemes that restrict attention to $T$ of order $\hat p$.

## Sources

- J. Mathews, S. C. Schmidler, "Posterior bounds on divergence time of two sequences under dependent-site evolutionary models", arXiv preprint (2025), Theorem 1, Theorem 2, Theorem 3 (Section 4), <https://doi.org/10.48550/arXiv.2507.19659>.
