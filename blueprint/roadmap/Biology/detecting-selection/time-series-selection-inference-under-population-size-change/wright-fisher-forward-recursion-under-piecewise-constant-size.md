# Wright–Fisher forward recursion for allele counts under piecewise-constant size

**Model.** A biallelic locus (alleles $a$, $A$) evolves in a diploid population whose history is split into epochs $\ell = 1,\dots,L$ on time intervals $[\tau_{\ell-1},\tau_\ell]$ with constant size $N_\ell$, mutation probabilities $u_{aA}^{(\ell)}, u_{Aa}^{(\ell)}$, selection coefficient $s_\ell$ and dominance $h_\ell$ (fitnesses $1+s_\ell$, $1+h_\ell s_\ell$, $1$ for $AA$, $aA$, $aa$). If the count of $A$ in generation $t$ is $c_t = i$, the post-mutation gamete frequency is

$$f^t_{A|i} = u^{(t)}_{aA} + \big(1-u^{(t)}_{Aa}-u^{(t)}_{aA}\big)\frac{i}{2N_t},$$

genotypes after random mating and selection have frequencies $p^t_{AA|i} = (f^t_{A|i})^2(1+s_t)/\bar w_{t,i}$, $p^t_{Aa|i} = 2f^t_{A|i}(1-f^t_{A|i})(1+h_ts_t)/\bar w_{t,i}$, $p^t_{aa|i} = (1-f^t_{A|i})^2/\bar w_{t,i}$, and with $p^t_{A|i} = p^t_{AA|i} + \tfrac12 p^t_{Aa|i}$ drift gives

$$\Pr(C_{t+1} = j \mid C_t = i) = \binom{2N_{t+1}}{j}\,(p^t_{A|i})^j(1-p^t_{A|i})^{2N_{t+1}-j},$$

the entries of a $(2N_t+1)\times(2N_{t+1}+1)$ transition matrix $T_{t,t+1}$ (rectangular across an epoch boundary).

**Data.** Samples of $n_k$ haplotypes at integer times $t_1 < \dots < t_K$ show $o_k$ copies of $A$, with binomial emission $\gamma_i(o_k) = \binom{n_k}{o_k}(i/2N_{t_k})^{o_k}(1-i/2N_{t_k})^{n_k-o_k}$.

**Proposition (forward procedure).** Let $v_{k,i} = \Pr(O_{[1:k]} = o_{[1:k]},\, C_{t_k} = i)$ and $d_0$ the initial count distribution. Then

$$v_1 = d_0\Big[\prod_{t=1}^{t_1} T_{t-1,t}\Big]\operatorname{diag}\gamma(o_1), \qquad v_k = v_{k-1}\Big[\prod_{t=t_{k-1}+1}^{t_k} T_{t-1,t}\Big]\operatorname{diag}\gamma(o_k),$$

and the likelihood is $\Pr(O_{[1:K]} = o_{[1:K]}) = \sum_{i} v_{K,i}$.

## Depends on

- [Hidden Markov likelihood for allele-frequency time series](../selection-from-allele-frequency-time-series/hmm-likelihood-for-allele-frequency-time-series.md)

## Proof depends on

- [The forward algorithm computes the likelihood](../../../ComputerScience/machine-learning/probabilistic-graphical-models/hidden-markov-models/likelihood-eq-sum-forward.md)

## Expansion

This is the standard HMM forward algorithm with the population count as hidden state. Because only row vectors are propagated, the products of transition matrices are never formed: each generation costs one vector–matrix product, which keeps exact Wright–Fisher computation feasible for realistic population sizes and lets the matrix dimensions change with $N_t$ from epoch to epoch.

## Sources

- E. M. Jewett, M. Steinrücken, Y. S. Song, "The effects of population size histories on estimates of selection coefficients from time-series genetic data", Molecular Biology and Evolution 33(11) (2016) 3002–3027, Methods, Eqs (2)–(10) and Procedure 1, <https://doi.org/10.1093/molbev/msw173>, PMCID PMC5062326.
