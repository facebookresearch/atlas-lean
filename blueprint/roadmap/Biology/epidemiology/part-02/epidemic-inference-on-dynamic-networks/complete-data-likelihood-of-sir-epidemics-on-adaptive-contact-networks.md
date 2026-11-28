# Complete-data likelihood of SIR epidemics on adaptive contact networks

**Model.** A closed population of $N$ individuals has an evolving contact network and SIR disease states. Write $H(t)=S(t)+R(t)$ for the healthy (non-infectious) individuals. Each susceptible becomes infected at rate $\beta$ times its number of infectious neighbours, and each infective recovers at rate $\gamma$. Links rewire depending on the disease status of their endpoints: an absent link between two healthy individuals, a healthy and an infective, or two infectives appears at rate $\alpha_{SS}$, $\alpha_{SI}$, $\alpha_{II}$ respectively, and an existing link of the corresponding type disappears at rate $\omega_{SS}$, $\omega_{SI}$, $\omega_{II}$. Let $M_{HH}(t),M_{HI}(t),M_{II}(t)$ be the current numbers of links of each type, $SI(t)$ the number of susceptible–infective links, and record all events at times $t_1<\dots<t_n$.

**Likelihood.** Given the initial network and one initial infective, with $n_E$ infections (including the index case), $n_R$ recoveries, $C_{\cdot\cdot}$ link activations and $D_{\cdot\cdot}$ link deletions of each type, the complete-data likelihood is

$$
\mathcal L\propto\gamma^{n_R}\beta^{n_E-1}\prod_{\cdot\cdot}\alpha_{\cdot\cdot}^{C_{\cdot\cdot}}\omega_{\cdot\cdot}^{D_{\cdot\cdot}}\exp\Big(-\int_0^{T_{\max}}\big[\beta\,SI(t)+\gamma I(t)+\tilde\alpha^{\top}\mathbf M_{\max}(t)+(\tilde\omega-\tilde\alpha)^{\top}\mathbf M(t)\big]dt\Big),
$$

where $\mathbf M_{\max}=\big(\binom{H}{2},HI,\binom{I}{2}\big)$ counts possible links of each type and $\mathbf M=(M_{HH},M_{HI},M_{II})$.

**Theorem (maximum likelihood).** With complete event data, the MLEs are ratios of event counts to exposure times, for example

$$
\hat\beta=\frac{n_E-1}{\sum_jSI(t_j)(t_j-t_{j-1})},\qquad \hat\gamma=\frac{n_R}{\sum_jI(t_j)(t_j-t_{j-1})},\qquad \hat\alpha_{SS}=\frac{C_{HH}}{\sum_j\big[\binom{H(t_j)}{2}-M_{HH}(t_j)\big]\,(t_j-t_{j-1})},\qquad \hat\omega_{SS}=\frac{D_{HH}}{\sum_jM_{HH}(t_j)(t_j-t_{j-1})},
$$

and analogously for the $SI$ and $II$ link rates.

**Theorem (conjugate Bayesian inference).** Under independent Gamma priors $\beta\sim\mathrm{Ga}(a_\beta,b_\beta)$, $\gamma\sim\mathrm{Ga}(a_\gamma,b_\gamma)$, $\alpha_{\cdot\cdot}\sim\mathrm{Ga}(a_\alpha,b_\alpha)$, $\omega_{\cdot\cdot}\sim\mathrm{Ga}(a_\omega,b_\omega)$, the posteriors are Gamma, e.g. $\beta\mid\text{data}\sim\mathrm{Ga}\big(a_\beta+n_E-1,\ b_\beta+(n_E-1)/\hat\beta\big)$ and $\omega_{SS}\mid\text{data}\sim\mathrm{Ga}\big(a_\omega+D_{HH},\ b_\omega+D_{HH}/\hat\omega_{SS}\big)$.

## Expansion

The coupled process is a continuous-time Markov chain whose transitions are infections, recoveries, and link additions and deletions of three types; its path density is the product of the rates of observed events times $\exp(-\int\text{total rate})$. Every rate is a parameter times a count of eligible units (S–I links, infectives, absent or present links of a type), so the log-likelihood separates into independent Poisson-process terms, one per parameter. Each term has the form $c\log\theta-\theta E$, giving $\hat\theta=c/E$ and Gamma conjugacy. When only periodic disease-status reports are available, these closed forms become the complete-data step of a data-augmentation sampler that imputes recovery times.

## Proof depends on

- [Gamma–Poisson conjugacy with exposure](../../../../Probability/bayesian-statistics/gamma-poisson-counts-and-empirical-bayes-shrinka/posterior-eq-gamma-pdfreal.md)

## Sources

- Fan Bu, Allison E. Aiello, Jason Xu, Alexander Volfovsky, "Likelihood-based Inference for Partially Observed Epidemics on Dynamic Networks", arXiv:1910.04221: Section on epidemic processes over adaptive networks: complete-data likelihood (SIR) and the theorems on maximum likelihood estimation and Bayesian inference with conjugate priors. <https://doi.org/10.48550/arXiv.1910.04221>
