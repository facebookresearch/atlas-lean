# Consistency and effective sample size of online phylogenetic sequential Monte Carlo

**Setting.** Let $\mathcal T_n$ be the space of rooted binary phylogenetic trees with branch lengths on the first $n$ sequences, $\bar\pi_n$ the posterior on $\mathcal T_n$ (likelihood times prior), and $\hat\pi_n$ its unnormalized version. *Online phylogenetic SMC* (OPSMC) updates a weighted particle approximation $\bar\pi_{n,K}$ of $\bar\pi_n$ to one of $\bar\pi_{n+1}$ when sequence $n+1$ arrives: each particle $r\in\mathcal T_n$ is extended to $t=T(r,e,x,y)\in\mathcal T_{n+1}$ by attaching the new leaf to edge $e$ at distal position $x$ with pendant length $y\in[0,b]$, drawn from a proposal $Q^n(r,t)$, reweighted by

$$w(t)=\frac{\hat\pi_{n+1}(t)}{\hat\pi_n(\varrho(t))\,Q^n(\varrho(t),t)},$$

where $\varrho(t)$ is the parent tree obtained by removing the new leaf, then resampled and moved by a Markov kernel $P^n$.

**Criteria.** (i) $Q^n(r,r')>0$ if and only if $r'$ is obtained from $r$ by one leaf attachment; (ii) $P^n$ leaves $\bar\pi_n$ invariant.

**Theorem (consistency).** Under (i)–(ii), if the sampler starts from the empty tree, or at $n=1$ from an ergodic MCMC ensemble targeting $\bar\pi_1$, then for every integrable $\phi:\mathcal T_n\to\mathbb R$ and $n\le N$,

$$\bar\pi_{n,K_n}(\phi)\to\bar\pi_n(\phi)\qquad\text{as }K_1,\dots,K_n\to\infty .$$

**Theorem (asymptotic ESS).** With $\mathrm{ESS}_{n+1}=(\sum_iw_i)^2/\sum_iw_i^2$,

$$\lim_{K\to\infty}\frac{K_{n+1}}{\mathrm{ESS}_{n+1}}=\int_{\mathcal T_{n+1}}\frac{\bar\pi_{n+1}(t)^2}{\bar\pi_n(\varrho(t))\,Q^n(\varrho(t),t)}\,dt .$$

**Theorem (ESS lower bounds).** Assume the posterior mean of the average branch length $\zeta$ is bounded below, $\int\bar\pi_n\zeta\ge c>0$ uniformly in $n$.
1. *Likelihood-based proposals* (edge chosen proportionally to a utility comparable to the maximal attachment likelihood on that edge, with attachment densities bounded below): there is $\alpha>0$ independent of $n$ with $\mathrm{ESS}_n\ge\alpha K_n$.
2. *Length-based proposals* (edge chosen proportionally to its length, distal and pendant densities with $l_e^{-2}\int_0^{l_e}p_X^e(x)^{-1}dx\le C$ and $\int p_Y^{-1}<\infty$): $\mathrm{ESS}_n\ge\alpha K_n$ as well.

Without the branch-length condition, the ESS decays at most linearly (likelihood-based) or quadratically (length-based) in the number of taxa.

## Expansion

Consistency is an induction over $n$ along the standard SMC chain (proposal, weighting, resampling, invariant MCMC move), using that each $t\in\mathcal T_{n+1}$ has a unique parent. The change of variables $(r,e,x,y)\mapsto T(r,e,x,y)$ is a bijection with $d\mu_{n+1}=\frac{V_n}{V_{n+1}}\,dx\,dy\,de\,d\mu_n$, $V_n=(2n-3)!!$, which lets the posterior ratio be bounded: with $M(y),m(y)$ the largest and smallest transition probabilities over a pendant edge of length $y$ and $S$ sites,

$$\frac{\bar\pi_{n+1}(t)}{\bar\pi_n(\varrho(t))}\le\frac{1}{\mathcal Z_n}\,\frac{M(y)^S}{\int_0^bm(y)^S\,dy},\qquad \mathcal Z_n=\int\bar\pi_n\zeta .$$

Adding a sequence therefore changes the likelihood surface by a bounded factor, which keeps the chi-square-type integral in the ESS limit bounded.

## Sources

- Vu Dinh, Aaron E Darling, Frederick A Matsen IV, "Online Bayesian Phylogenetic Inference: Theoretical Foundations via Sequential Monte Carlo", Systematic Biology 67 (2018), 503–517, <https://doi.org/10.1093/sysbio/syx087>. Published version of arXiv:1610.08148, cited next; locators there refer to the arXiv version.
- Vu Dinh, Aaron E. Darling, Frederick A. Matsen IV, "Online Bayesian phylogenetic inference: theoretical foundations via Sequential Monte Carlo", arXiv:1610.08148 (2016): Criteria 3.1 and 3.7, Theorem 4.2 (consistency), Lemmas 5.1–5.2, Theorems 6.1–6.3. <https://doi.org/10.48550/arXiv.1610.08148>
