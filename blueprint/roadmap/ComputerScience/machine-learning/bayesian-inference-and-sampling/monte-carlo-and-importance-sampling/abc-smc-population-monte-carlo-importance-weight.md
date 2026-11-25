# ABC population Monte Carlo importance weights

Let $\pi$ be a prior density on a parameter space $\Theta\subseteq\mathbb R^d$, let $\theta\mapsto P_\theta$ be a kernel of simulated data, $y$ the observed data, $\rho$ a measurable discrepancy, and $\varepsilon_1>\dots>\varepsilon_T\ge0$ fixed (non-adaptive) tolerances. As in [rejection ABC](../rejection-sampling/abc-rejection-target-law-and-zero-tolerance-disc.md), the tolerance-$\varepsilon$ target is

$$\pi_\varepsilon(\theta)\propto\pi(\theta)\,a_\varepsilon(\theta),\qquad a_\varepsilon(\theta)=P_\theta\bigl(\rho(X,y)\le\varepsilon\bigr),$$

assumed normalizable. Let $K_t(\theta',\theta)$ be perturbation kernel densities with $K_t(\theta',\theta)>0$ whenever $\pi(\theta)>0$.

The ABC population Monte Carlo (ABC-SMC) sampler with $N$ particles is defined as follows. At $t=1$, run rejection ABC with tolerance $\varepsilon_1$ to obtain $\theta_1^1,\dots,\theta_1^N$ with weights $W_1^i=1/N$. At $t\ge2$, repeat until $N$ particles are accepted: draw $\theta^*$ from $\{\theta_{t-1}^j\}$ with probabilities $W_{t-1}^j$, draw $\theta\sim K_t(\theta^*,\cdot)$, simulate $X\sim P_\theta$, and accept $\theta$ if $\rho(X,y)\le\varepsilon_t$. Give the accepted $\theta_t^i$ the weights

$$w_t^i=\frac{\pi(\theta_t^i)}{\sum_{j=1}^NW_{t-1}^j\,K_t(\theta_{t-1}^j,\theta_t^i)},\qquad W_t^i=\frac{w_t^i}{\sum_kw_t^k}.$$

These weights satisfy the importance-weight identity for $\pi_{\varepsilon_t}$. Given generation $t-1$, the accepted particles are iid with density proportional to $q_t(\theta)\,a_{\varepsilon_t}(\theta)$, where $q_t(\theta)=\sum_jW_{t-1}^jK_t(\theta_{t-1}^j,\theta)$, and for every bounded measurable $h$,

$$\frac{\mathbb E[w_t^i\,h(\theta_t^i)\mid\text{generation }t-1]}{\mathbb E[w_t^i\mid\text{generation }t-1]}=\int h\,d\pi_{\varepsilon_t}.$$

If moreover $K_t(\theta',\theta)\ge c_t\,\pi(\theta)$ for all $\theta$, all $\theta'$ with $\pi(\theta')>0$, and some $c_t>0$, then $\sum_iW_t^ih(\theta_t^i)\to\int h\,d\pi_{\varepsilon_t}$ in probability as $N\to\infty$, for each fixed $t$. For $T=1$ the sampler is rejection ABC. Beaumont et al. (2009) introduced these weights to correct a bias in the earlier likelihood-free sequential weighting of Sisson et al. (2007); data-adaptive tolerances are not covered.

## Depends on

- [Rejection ABC returns the tolerance-conditioned posterior](../rejection-sampling/abc-rejection-target-law-and-zero-tolerance-disc.md)

## Proof depends on

- [SMC sampler: unbiasedness of the normalizing-constant estimator](smc-sampler-unbiasedness-of-the-normalizing-cons.md)
- [Self-normalized importance sampling: ratio consistency, O(1/n) bias, effective sample size](self-normalized-importance-sampling-ratio-consis.md)

## Expansion

A full page proves the conditional law of an accepted particle (a rejection step applied to the mixture proposal $q_t$), the importance-weight identity, and consistency from the conditional variance of a self-normalized estimator with weights bounded by $1/c_t$. It should

- verify the identity on a two-point prior with explicit acceptance probabilities;
- show that $T=1$ reduces to rejection ABC;
- compare the bounded-ratio hypothesis with the conditions of Beaumont et al. (2009) and replace it by theirs if weaker.

## Sources

- M. A. Beaumont, J.-M. Cornuet, J.-M. Marin and C. P. Robert, *Adaptive approximate Bayesian computation* (2009), corrected PMC weights.
- S. A. Sisson, Y. Fan and M. M. Tanaka, *Sequential Monte Carlo without likelihoods* (2007), <https://pubmed.ncbi.nlm.nih.gov/17264216/>, ABC-SMC.
