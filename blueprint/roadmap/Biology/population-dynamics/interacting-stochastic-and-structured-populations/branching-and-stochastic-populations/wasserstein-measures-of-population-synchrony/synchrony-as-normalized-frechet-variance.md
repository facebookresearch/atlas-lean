# Synchrony as normalized Frechet variance

**Definition.** Let $(M,d)$ be a compact metric space of individual states (cell-cycle phases, developmental stages, positions) with at least two points, and let $\pi\in\mathcal P(M)$ be the distribution of a population over $M$. The generalized (Frechet) variance and the synchrony of $\pi$ are

$$\operatorname{Var}(\pi)=\inf_{\alpha\in M}\int_Md(x,\alpha)^2\,d\pi(x)=\inf_{\alpha\in M}W_2(\pi,\delta_\alpha)^2,\qquad F(\pi)=1-\frac{\operatorname{Var}(\pi)^{1/2}}{\nu},\quad \nu=\sup_{\pi'\in\mathcal P(M)}\operatorname{Var}(\pi')^{1/2},$$

where $W_2$ is the Wasserstein-2 distance; $1-F(\pi)$ is the asynchrony.

**Properties.**

1. *Continuity.* $F$ is continuous on $\mathcal P(M)$ with the weak* topology; the supremum $\nu>0$ is attained.
2. *Interpretability.* $\operatorname{Var}(\pi)=0$ iff $\pi=\delta_\alpha$ for some $\alpha$, so $F(\pi)=1$ exactly for a perfectly synchronized population, $F\in[0,1]$, and $F=0$ for a maximally asynchronous one.
3. *Scale invariance.* Replacing $d$ by $\lambda d$, $\lambda>0$, leaves $F$ unchanged.
4. *Approximability.* If $X\subset M$ is compact and $g:M\to X$ is measurable with $d(x,g(x))\le\varepsilon$ for all $x$, then $|F_{(M,d)}(\pi)-F_{(X,d)}(g_*\pi)|\le3\varepsilon/\nu_{(M,d)}$.
5. *Circle.* On the circle of circumference one with arc-length metric, the uniform distribution is the unique maximizer of $\operatorname{Var}$, with $\operatorname{Var}=1/12$ and $\nu=\sqrt3/6$. On the discrete circle $\{0,\dots,p-1\}$ with $d_p(x,y)=\min(|x-y|/p,1-|x-y|/p)$, the uniform distribution also maximizes $\operatorname{Var}$, so $\nu_p^2=\frac1p\sum_{i=0}^{p-1}\min(i/p,1-i/p)^2$, and binning phases into $p$ stages changes synchrony by less than $3\sqrt3/p$.

## Expansion

$\operatorname{Var}$ is the squared $W_2$ distance from $\pi$ to the nearest Dirac mass, so synchrony measures how far the population is from all individuals sharing one state, normalized by the worst case on the same state space. Continuity follows from continuity of $(\pi,\alpha)\mapsto\int d(x,\alpha)^2d\pi$ and compactness; scale invariance is because numerator and normalizer scale by $\lambda$. Approximability rests on the coupling bound $W_2(\pi,g_*\pi)\le\varepsilon$ and the triangle inequality for $W_2$. On the circle the classical mean-resultant-length measures (Kuramoto order parameter) do not extend to stage-structured or non-cyclic state spaces; this definition does, and it can be computed exactly for empirical distributions on finite metric spaces and on the circle.

## Sources

- Francis C. Motta, Kevin McGoff, Breschine Cummins, Steven B. Haase, "Generalized Measures of Population Synchrony", *Mathematical Biosciences* 380 (2025), 109344, Definition 1 and Propositions 1-6 (Sections 2-4), <https://doi.org/10.1016/j.mbs.2024.109344> (preprint arXiv:2406.15987).
