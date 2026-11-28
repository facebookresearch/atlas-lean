# Tempered, importance-weighted acceptance in sequential ABC

**Setting.** As for the stochastic acceptor: prior $\pi(\theta)$, simulator $p(y \mid \theta)$, noise density $\pi(D \mid y, \theta)$ evaluated at the data. A sequential Monte Carlo ABC scheme runs iterations $t = 1, \dots, n_t$ with temperatures $T_1 > T_2 > \dots > T_{n_t} = 1$ and proposals $g_t(\theta)$ (a mixture of perturbation kernels around the previous weighted population, with $g_1 = \pi$). Iteration $t$ targets the tempered distribution

$$\pi_{\mathrm{ABC}, t}(\theta \mid D) \ \propto\ \int \pi(D \mid y, \theta)^{1/T_t}\, p(y \mid \theta)\, \pi(\theta)\, dy , \tag{1}$$

which equals the exact posterior at $T_{n_t} = 1$.

**Theorem (importance-weighted acceptance).** Let $c_t > 0$ be arbitrary. Draw $\theta \sim g_t$, simulate $y \sim p(y \mid \theta)$, accept with probability

$$a_t(y, \theta) = \min\Big[\Big(\frac{\pi(D \mid y, \theta)}{c_t}\Big)^{1/T_t},\ 1\Big],$$

and give an accepted particle the weight

$$w_t(y, \theta) \ \propto\ \frac{\pi(D \mid y, \theta)^{1/T_t}}{a_t(y, \theta)} \cdot \frac{\pi(\theta)}{g_t(\theta)} .$$

Then the weighted accepted particles target (1). In particular $c_t$ need not bound the noise density: a value below the maximum raises acceptance rates while the weights correct the "decapitation" of the acceptance kernel, at the price of weight degeneracy (lower effective sample size $(\sum w_i)^2 / \sum w_i^2$).

**Adaptive choices.** $c_t$ is set to the largest value of $\pi(D \mid y, \theta)$ seen so far (optionally scaled down when acceptance is too low). The next temperature is the minimum of (i) the $T$ for which the importance-sampling estimate of the expected acceptance rate

$$\gamma(T) \approx \frac1N \sum_{i=1}^N \frac{g_t(\theta_i^{(t-1)})}{g_{t-1}(\theta_i^{(t-1)})} \min\Big[\Big(\frac{\pi(D \mid y_i^{(t-1)}, \theta_i^{(t-1)})}{c_t}\Big)^{1/T}, 1\Big]$$

matches a target rate, using all particles of the previous iteration including rejected ones, and (ii) a geometric decay $T_{t+1} = \alpha T_t$ with $\alpha \in (0,1)$, which guarantees $T \to 1$. The initial temperature is found by applying (i) to a calibration sample from the prior.

## Expansion

The density of accepted particles before weighting is $g_t(\theta)\, p(y \mid \theta)\, a_t(y, \theta)$; multiplying by $w_t$ gives $p(y \mid \theta)\, \pi(D \mid y, \theta)^{1/T_t}\, \pi(\theta)$, whose $\theta$-marginal is (1). When $c_t \ge \sup \pi(D \mid y,\theta)$ the minimum is never active and the weight reduces to the usual $\pi(\theta)/g_t(\theta)$ times a constant. Tempering raises acceptance for every noise model except the uniform one, where it changes nothing (and standard ABC already applies). On four test models (ODE and chemical-master-equation), the self-tuned sampler needed the fewest simulations, about 2 to 22 times fewer than exact rejection ABC; fixing $c$ at the mode of the noise density would have required up to 20 orders of magnitude more simulations, and that mode grows exponentially with the number of data points while the self-tuned $c_t$ does not. The noise-randomized sampler (A2) gave different posteriors on three of the four models within the same budget.

## Depends on

- [Exact approximate Bayesian computation with a stochastic acceptor for measurement noise](stochastic-acceptor-gives-exact-noisy-abc.md)
## Sources

- Y. Schälte, J. Hasenauer, "Efficient exact inference for dynamical systems with noisy measurements using sequential approximate Bayesian computation", Bioinformatics 36 (Suppl. 1) (2020), i551–i559, Section 2.5 (Eq. (1)), Section 2.6 (Theorem 2, Eq. (2)) and Section 2.7 (Eq. (3), temperature schemes), <https://doi.org/10.1093/bioinformatics/btaa397> (PMC7355286).
