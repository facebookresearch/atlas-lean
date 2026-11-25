# Stationary-kernel discretization for pairwise SMC hidden Markov models

A supplied stationary pairwise-TMRCA kernel determines a finite-state hidden Markov model by conditioning on time intervals. This construction has exactly stationary interval masses and an exact forward likelihood for the constructed model. It is an ideal stationary-kernel discretization, not a claim that every transition or emission approximation in the PSMC software has the same law.

## Kernel, grid and stationary masses

Let $R(s,dt)$ be a measurable probability kernel on $[0,\infty)$ and let $\nu$ be a probability law satisfying $\nu R=\nu$. For an SMC application, $R$ must be the appropriate fixed-genomic-distance transition kernel with this invariant law, not merely a kernel conditional on one recombination event. Fix a finite grid $0=\tau_0<\cdots<\tau_K<\tau_{K+1}=\infty$ and $I_i=[\tau_i,\tau_{i+1})$. Put

$$\pi_i=\nu(I_i),\qquad P_{ij}=\frac{1}{\pi_i}\int_{I_i}R(s,I_j)\,\nu(ds)\quad(\pi_i>0).$$

For a zero-mass interval choose any probability row, for example $P_{ii}=1$. Nonnegativity and the partition identity give $\sum_jP_{ij}=1$, including the chosen zero-mass rows. Stationarity follows without any lumpability assumption:

$$\sum_i\pi_iP_{ij}=\int R(s,I_j)\,\nu(ds)=(\nu R)(I_j)=\pi_j.$$

In the ideal constant-size, coalescent-unit case with $\nu=\mathrm{Exp}(1)$, this gives $\pi_i=e^{-\tau_i}-e^{-\tau_{i+1}}$ for $i<K$ and $\pi_K=e^{-\tau_K}$. All these masses are positive. For a strictly positive piecewise-constant size history $\lambda(t)=\lambda_i$ on $I_i$, the ideal coalescent marginal has density $\lambda(t)^{-1}e^{-H(t)}$, where $H(t)=\int_0^t\lambda(u)^{-1}du$. Its interval masses are $e^{-H(\tau_i)}-e^{-H(\tau_{i+1})}$, with $e^{-H(\infty)}=0$. Using this marginal requires a supplied kernel invariant for it; the positive final $\lambda_K$ ensures a proper finite-TMRCA law.

## Poisson emissions and missing observations

Assume a bin has one TMRCA and an infinite-sites Poisson mutation count conditional on it: $M\mid T=t\sim\mathrm{Poisson}(\theta t)$ with $\theta\ge0$, including bin length in the scaled mutation parameter. The binary observation is $1$ if $M\ge1$ and $0$ otherwise. For $\pi_i>0$, define

$$e_i(0)=\frac{1}{\pi_i}\int_{I_i}e^{-\theta t}\,\nu(dt),\qquad e_i(1)=1-e_i(0).$$

These numbers lie in $[0,1]$ and sum to one. On a zero-mass state choose $e_i(0)=1$, $e_i(1)=0$. In the ideal piecewise-size marginal above, writing $r_i=1/\lambda_i$ and $\Delta_i=\tau_{i+1}-\tau_i$, the exact finite-interval average is

$$e_i(0)=e^{-\theta\tau_i}\frac{r_i}{r_i+\theta}\frac{1-e^{-(r_i+\theta)\Delta_i}}{1-e^{-r_i\Delta_i}}\quad(i<K),\qquad e_K(0)=e^{-\theta\tau_K}\frac{r_K}{r_K+\theta}.$$

In particular, $\theta=0$ gives only zero observations. For a fixed ignorable missing-data mask, use likelihood weight $e_i(\mathtt{missing})=e_i(0)+e_i(1)=1$. This is marginalization of an unobserved binary value, **not** a third outcome of a normalized three-symbol emission distribution. Informative missingness needs its own model. The Poisson rule concerns segregating mutations under these assumptions, not a general finite-sites substitution or within-bin recombination model.

## The finite HMM likelihood

Define a finite hidden chain with initial distribution $\pi$ and transition matrix $P$, and conditionally independent binary emissions given its states with probabilities $e_i$. This supplies weights for the [HMM](../hidden-markov-models/hmm.md); its generic weight structure alone does not impose normalization. For observations $x_0,\dots,x_{n-1}$, including the fixed missing mask, the constructed-model likelihood is

$$L(x)=\sum_{z_0,\dots,z_{n-1}}\pi_{z_0}\left(\prod_{b=0}^{n-2}P_{z_bz_{b+1}}\right)\left(\prod_{b=0}^{n-1}e_{z_b}(x_b)\right).$$

For $n\ge1$, initialize $a_0(i)=\pi_i e_i(x_0)$ and update $a_{b+1}(j)=e_j(x_{b+1})\sum_i a_b(i)P_{ij}$. The [forward identity](../hidden-markov-models/likelihood-eq-sum-forward.md) gives $L=\sum_i a_{n-1}(i)$; the [forward-backward identity](../hidden-markov-models/likelihood-eq-sum-forward-mul-backward.md) also applies. The empty observation sequence has likelihood one. Posterior conditioning and EM calculations require positive observed likelihood where a division or logarithm is taken.

Although $P$ matches the stationary two-bin law, the interval labels of the original continuous-state chain need not themselves be Markov. For example, bin a stationary deterministic three-cycle $0\to1\to2\to0$ into $A=\{0,1\}$ and $B=\{2\}$. Its conditional matrix has $P_{AA}=P_{AB}=1/2$ and $P_{BA}=1$, but the true probability of $AAA$ is zero whereas the aggregated Markov model gives $1/6$. Likewise, interval-averaged emissions do not by themselves establish the conditional-independence structure of the projected observation process. No equality with its full likelihood, or with the full ancestral recombination graph likelihood, is claimed.

## Relation to the PSMC approximation

The source's one-event-per-step approximation must be distinguished from the ideal fixed-distance SMC semigroup. At constant size, for $s>0$, let $K(s,\cdot)$ be the law of $U+Z$ with independent $U\sim\mathrm{Uniform}(0,s)$ and $Z\sim\mathrm{Exp}(1)$. For $\rho>0$, the normalized kernel

$$R_\rho(s,dt)=(1-e^{-\rho s})K(s,dt)+e^{-\rho s}\delta_s(dt)$$

with $R_\rho(0,\cdot)=\delta_0$, has stationary density proportional to $t e^{-t}/(1-e^{-\rho t})$, not $e^{-t}$. The event kernel preserves the density $t e^{-t}$; dividing it by the event probability compensates for holding. Indeed, starting with $T\sim\mathrm{Exp}(1)$ gives $\mathbb E[T']-1=\rho^2/[2(1+\rho)^2]>0$. Conditioning this kernel using its actual stationary law is valid; exponential interval masses cannot in general be asserted to be exactly stationary for it. Exponential masses belong to the ideal continuous-distance model and the appropriate small-step limit.

The author's implementation uses approximated stationary interval masses and emissions at a representative time, rather than the exact conditional averages defined above. Its code assigns $e(0)=e^{-\theta t_*}$ and $e(1)=1-e^{-\theta t_*}$, consistent with the Poisson convention; the reversed labels in the article's displayed Methods expression are not adopted. PSMC uses EM-based numerical fitting of constrained demographic parameters. This does not establish an exact global maximum, unrestricted Baum-Welch re-estimation, or a convergence guarantee for that optimizer.

## Depends on

- [Hidden Markov model](../hidden-markov-models/hmm.md)
- [Likelihood of the observations](../hidden-markov-models/likelihood.md)

## Proof depends on

- [The forward algorithm computes the likelihood](../hidden-markov-models/likelihood-eq-sum-forward.md)
- [The likelihood from the forward and backward variables](../hidden-markov-models/likelihood-eq-sum-forward-mul-backward.md)

## Related

- [The number of segregating sites is conditionally Poisson](../../../../Biology/coalescent-theory/poisson-mutation-on-the-kingman-genealogy/has-cond-distrib-seg-sites-of-mutation.md), whose two-lineage constant-size specialization gives total mutation mean $\theta T$.

## Sources

- H. Li and R. Durbin, *Inference of human population history from individual whole-genome sequences*, Nature 475 (2011), 493–496, <https://pmc.ncbi.nlm.nih.gov/articles/PMC3154645/>, Online Methods, PSMC overview and parameter fitting.
- The author's [PSMC derivation](https://github.com/lh3/psmc/blob/82fa2ada83ee463fe1251b562ae3d60e82d7ad6a/psmc.tex), the stationary laws and discrete-time approximation, and [implementation](https://github.com/lh3/psmc/blob/82fa2ada83ee463fe1251b562ae3d60e82d7ad6a/core.c), `psmc_update_hmm`. These distinguish the approximation from the exact conditional-aggregation construction above.
