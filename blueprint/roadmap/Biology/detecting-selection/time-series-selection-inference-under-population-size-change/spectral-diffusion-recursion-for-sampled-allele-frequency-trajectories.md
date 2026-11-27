# Spectral diffusion recursion for sampled allele frequency trajectories

**Setting.** In the diffusion limit of the epoch model, the population frequency $Y_t$ of allele $A$ has transition density $p_\Theta(s,t;x,y)$, $p_\Theta(s,t;x,y)\,dy = \Pr(y \le Y_t < y+dy \mid Y_s = x)$. Samples of $n_k$ haplotypes at times $t_1<\dots<t_K$ show $o_k$ copies of $A$. Define the forward densities

$$f_k(y)\,dy = \Pr\big(O_{[1:k]} = o_{[1:k]},\; y \le Y_{t_k} < y+dy\big), \qquad g_k(y)\,dy = \Pr\big(O_{[1:k-1]} = o_{[1:k-1]},\; y \le Y_{t_k} < y+dy\big).$$

**Proposition.**

$$f_k(y) = g_k(y)\binom{n_k}{o_k} y^{o_k}(1-y)^{n_k-o_k}, \qquad g_k(y) = \int_0^1 f_{k-1}(z)\, p_\Theta(t_{k-1},t_k;z,y)\,dz,$$

and the likelihood of the data is $\int_0^1 f_K(y)\,dy$.

**Spectral form.** Let $B_{\ell,i}$ ($i = 0,1,\dots$) be the eigenfunctions of the backward generator of epoch $\ell$ and $\pi_\ell$ its speed density. Writing

$$f_k(y) = \sum_{i\ge0} b_{k,i}\,\pi_{\ell_k}(y)B_{\ell_k,i}(y), \qquad g_k(y) = \sum_{i \ge 0} a_{k,i}\,\pi_{\ell_k}(y)B_{\ell_k,i}(y),$$

the recursion becomes a linear recursion on coefficient vectors $a_k, b_k$: within an epoch each coefficient is multiplied by $e^{-\lambda_{\ell,i}\Delta t}$ for the eigenvalue $\lambda_{\ell,i}$, the binomial emission acts as a fixed matrix on the basis, and at an epoch boundary the density is re-expanded in the new epoch's basis. If the frequency at the first sampling time is taken uniform on $[0,1]$, $b_1$ has a closed form.

## Depends on

- [Hidden Markov likelihood for allele-frequency time series](../selection-from-allele-frequency-time-series/hmm-likelihood-for-allele-frequency-time-series.md)
- [Wright–Fisher forward recursion for allele counts under piecewise-constant size](wright-fisher-forward-recursion-under-piecewise-constant-size.md)

## Proof depends on

- [Chapman–Kolmogorov equations, forward (law) form](../../../Probability/markov-chains/chapman-kolmogorov-equations/map-eq-bind-pow.md)

## Expansion

The emission step is binomial sampling of $n_k$ haplotypes from frequency $y$; the propagation step is the Chapman–Kolmogorov equation. Since the generator with selection and mutation is self-adjoint with respect to $\pi_\ell$, its transition density has the expansion $p(s,t;x,y) = \pi_\ell(y)\sum_i e^{-\lambda_{\ell,i}(t-s)}B_{\ell,i}(x)B_{\ell,i}(y)/\langle B_{\ell,i},B_{\ell,i}\rangle_{\pi_\ell}$, so integrating against $f_{k-1}$ reduces to scaling coefficients. Truncating the series gives an accurate likelihood without discretizing frequencies, and the epoch-change projection is what extends the constant-size method to bottlenecks, exponential growth and oscillating sizes.

## Sources

- E. M. Jewett, M. Steinrücken, Y. S. Song, "The effects of population size histories on estimates of selection coefficients from time-series genetic data", Molecular Biology and Evolution 33(11) (2016) 3002–3027, Methods, Eqs (12)–(19), Procedure 2, Lemma B.3.2 and Eq (B.17), <https://doi.org/10.1093/molbev/msw173>, PMCID PMC5062326.
