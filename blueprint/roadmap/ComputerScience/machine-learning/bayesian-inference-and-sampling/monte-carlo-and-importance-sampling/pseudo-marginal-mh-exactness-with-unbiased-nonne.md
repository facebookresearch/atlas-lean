# Exact posterior marginal of a pseudo-marginal Metropolis–Hastings chain

Let $\Theta,U$ be standard Borel spaces, $\lambda$ sigma-finite on
$\Theta$, $p$ a finite prior density, and $m_\theta$ a measurable probability
kernel on $U$. Let the jointly measurable finite estimator
$\widehat L(\theta,u)\ge0$ satisfy
$\int\widehat L(\theta,u)m_\theta(du)=L(\theta)$ and assume
$0<Z=\int p(\theta)L(\theta)\lambda(d\theta)<\infty$.
Then

$$\overline\pi(d\theta,du)
 =Z^{-1}p(\theta)\widehat L(\theta,u)m_\theta(du)\lambda(d\theta)$$

is a probability measure with exact posterior marginal
$Z^{-1}p(\theta)L(\theta)\lambda(d\theta)$.
Given current state $(\theta,u)$, propose $\theta'$ with density
$q(\theta,\theta')$ relative to $\lambda$, independently draw
$u'\sim m_{\theta'}$, and use acceptance probability

$$\min\left(1,
 \frac{p(\theta')\widehat L(\theta',u')q(\theta',\theta)}
 {p(\theta)\widehat L(\theta,u)q(\theta,\theta')}\right).$$

Use acceptance one when the denominator is zero, as in the general
MH convention. On rejection retain **both** $\theta$ and the old $u$;
on acceptance retain the proposed pair. This kernel is reversible and
invariant for $\overline\pi$. Therefore its parameter marginal at
stationarity is the exact posterior. This is not by itself a convergence
or mixing guarantee.

## Proof depends on

- [General-state Metropolis–Hastings with densities](../markov-chain-monte-carlo/general-state-metropolis-hastings-reversibility.md)

## Expansion

Use the fixed reference measure
$\Lambda(d\theta,du)=\lambda(d\theta)m_\theta(du)$, which is sigma-finite
because $\lambda$ is and each $m_\theta$ is a probability measure.
The target density relative to $\Lambda$ is $p\widehat L/Z$, and the
proposal density on the extended space is simply $q(\theta,\theta')$.
The linked theorem therefore applies even when the $m_\theta$ are not
dominated by a common measure on $U$. Tonelli and unbiasedness give the
claimed marginal. Estimator variance need not be finite for this target
identity, although it can affect mixing.

If $\widehat L=L$ deterministically, the parameter chain reduces to
ordinary MH. If its mean is instead $c(\theta)L(\theta)$, with finite
positive resulting evidence, the marginal is proportional to $pcL$;
it equals the desired posterior exactly when $c$ is constant almost
everywhere under that posterior. For example, a uniform two-point prior,
$L=(1,1)$ and $c=(1,2)$ give posterior weights $(1/3,2/3)$ rather than
$(1/2,1/2)$.

Refreshing the current estimate independently before every accept/reject
step is a different, generally inexact algorithm. For a two-point uniform
prior, a proposal that always flips the parameter, estimator $1$ at state
zero and estimator $1/2$ or $7/2$ with equal probabilities at state one,
the exact likelihoods are $(1,2)$ and the desired probability of state
one is $2/3$. Refreshing the current estimate each time gives transition
probabilities $P(0,1)=3/4$ and $P(1,0)=9/14$, hence stationary probability
$7/13$, not $2/3$.

## Sources

- C. Andrieu and G. O. Roberts, *The pseudo-marginal approach for efficient Monte Carlo computations* (2009), <https://doi.org/10.1214/07-AOS574>, <https://arxiv.org/abs/0903.5480>, equations (2.1)–(2.3), (2.9)–(2.10), and pp. 3–4 on retaining versus refreshing the auxiliary state. Equation (2.12) is a different comparison kernel using the tilted conditional auxiliary law, not the implementable kernel above. The finite counterexamples are derived here.
