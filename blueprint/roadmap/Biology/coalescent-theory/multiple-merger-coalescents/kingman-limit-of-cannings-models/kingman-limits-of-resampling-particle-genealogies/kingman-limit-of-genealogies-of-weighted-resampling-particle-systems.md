# Kingman limit of genealogies of weighted resampling particle systems

Consider an interacting particle system with $N$ particles per generation in which each particle at time $t$ chooses a parent at time $t-1$; let $\nu_t^{(i)}$ be the number of offspring of particle $i$ and $a_t$ the vector of parental indices. Fix $n \le N$ particles at the final time and let $G_t^{(n,N)}$ be the partition of $[n]$ in which $i, j$ share a block iff they have a common ancestor $t$ generations back.

**Standing assumption.** Conditional on the offspring counts $\boldsymbol\nu_t$, the parental index vector $a_t$ is uniform over all vectors with $\#\{j : a_t^{(j)} = i\} = \nu_t^{(i)}$ for every $i$ (true for any exchangeable resampling scheme, e.g. multinomial resampling, or after a uniform random relabelling).

With $(x)_k$ the falling factorial, define the pair-merger probability, the multiple-merger bound and the time change

$$c_N(t) = \frac{1}{(N)_2}\sum_{i=1}^N (\nu_t^{(i)})_2, \qquad D_N(t) = \frac{1}{N(N)_2}\sum_{i=1}^N (\nu_t^{(i)})_2\Big(\nu_t^{(i)} + \frac{1}{N}\sum_{j\ne i}(\nu_t^{(j)})^2\Big), \qquad \tau_N(t) = \min\Big\{s \ge 1 : \sum_{r=1}^s c_N(r) \ge t\Big\}.$$

**Theorem.** Under the standing assumption, suppose that for all $0 \le s < t < \infty$

$$\lim_{N\to\infty}\mathbb{E}\Big[\sum_{r=\tau_N(s)+1}^{\tau_N(t)} D_N(r)\Big] = 0, \qquad \lim_{N\to\infty}\mathbb{E}[c_N(t)] = 0, \qquad \lim_{N\to\infty}\mathbb{E}\Big[\sum_{r=\tau_N(s)+1}^{\tau_N(t)} c_N(r)^2\Big] = 0,$$

and $\mathbb{E}[\tau_N(t) - \tau_N(s)] \le C_{t,s}N$ for a constant independent of $N$. Then $(G^{(n,N)}_{\tau_N(t)})_{t\ge0}$ converges to Kingman's $n$-coalescent in the sense of finite-dimensional distributions as $N \to \infty$.

**Corollary (sequential Monte Carlo).** For SMC with multinomial resampling, if the potentials satisfy $a^{-1} \le g_t(x,x') \le a$ and the mutation kernels have densities with $\varepsilon h(x') \le q_t(x,x') \le \varepsilon^{-1}h(x')$ for a probability density $h$ and constants $0 < \varepsilon \le 1 \le a$, uniformly in $t$, then the hypotheses hold and genealogies of $n$ particles converge to Kingman's $n$-coalescent under the time change $\tau_N$.

## Depends on

- [Holding times of Kingman's coalescent](../../../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md)

## Expansion

Under the standing assumption, the conditional transition probability from partition $\xi$ to $\eta$ given $\boldsymbol\nu_t$ is a balls-in-boxes count, $p_{\xi\eta}(t) = (N)_{|\xi|}^{-1}\sum_{i_1,\dots,i_{|\eta|}\ \text{distinct}} \prod_k (\nu_t^{(i_k)})_{b_k}$, where $b_k$ blocks of $\xi$ merge into block $k$ of $\eta$. Elementary bounds show the probability of no merger is $1 - \binom{|\xi|}{2}c_N(t)$ up to $O(D_N)$ and $O(N^{-2})$ errors, a single binary merger has probability $c_N(t) + O(D_N)$, and anything else is $O(D_N)$. The time change accumulates pair-merger probability at unit rate, so summed over $[\tau_N(s), \tau_N(t)]$ the products of transition matrices converge to $e^{(t-s)Q}$ with $Q$ the Kingman rate matrix; the $c_N^2$ and $D_N$ conditions kill the error terms, and an optional-stopping argument handles the randomness of $\tau_N$. For multinomial resampling, $\mathbb{E}[c_N(t)\mid w_t] = \sum_i (w_t^{(i)})^2 = 1/\mathrm{ESS}(t)$, linking genealogy speed to the effective sample size.

## Sources

- Jere Koskela, Paul A. Jenkins, Adam M. Johansen and Dario Spanò, *Asymptotic genealogies of interacting particle systems with an application to sequential Monte Carlo*, Ann. Statist. 48(1) (2020), 560–583. <https://doi.org/10.1214/19-AOS1823> Section 2 (standing assumption, definitions of $c_N$, $D_N$, $\tau_N$), Lemma 1, Theorem 1, Lemma 3, Corollary 1. Erratum: Ann. Statist. 50(4) (2022), 2467–2468. <https://doi.org/10.1214/21-AOS2135> Locators use the numbering of the preprint arXiv:1804.01811. Its latest version includes the corrected argument.
