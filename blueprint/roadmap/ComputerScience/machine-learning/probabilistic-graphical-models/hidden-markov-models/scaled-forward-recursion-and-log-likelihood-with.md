# Scaled forward recursion: exact log-likelihood and filtering identities

Take a finite-state hidden Markov model with probability initial law
$\pi$, stochastic transition matrix $a$, and emission probabilities $b$.
For observations $x_0,x_1,\ldots$, let $\alpha_t$ be the
[unnormalized forward variables](likelihood-eq-sum-forward.md).
Set $\bar\alpha_0(s)=\pi(s)b(s,x_0)$,
$c_0=\sum_s\bar\alpha_0(s)$ and $\hat\alpha_0=\bar\alpha_0/c_0$.
For $t\ge1$, set
$\bar\alpha_t(s)=b(s,x_t)\sum_{s'}\hat\alpha_{t-1}(s')a(s',s)$,
$c_t=\sum_s\bar\alpha_t(s)$ and $\hat\alpha_t=\bar\alpha_t/c_t$.
Whenever $c_0,\ldots,c_t>0$,

$$\alpha_t=\left(\prod_{u=0}^tc_u\right)\hat\alpha_t,
\qquad L_t=\prod_{u=0}^tc_u,
\qquad\log L_t=\sum_{u=0}^t\log c_u.$$

Moreover $\hat\alpha_t$ is a probability vector and is the conditional
law of the hidden state at time $t$ given the observed prefix.
If the first zero normalizer occurs at $u$, that prefix and every longer
prefix have likelihood zero; the conditional filter is not defined there.

## Depends on

- [Forward likelihood identity](likelihood-eq-sum-forward.md)

## Expansion

The multiplicative relation follows by induction through the linear
forward recursion. Summing it gives $L_t$, and division by its positive
value is Bayes' formula for the filtering distribution.
These are exact-real identities. Scaling prevents multiplication of all
past likelihood factors into each state weight, but is **not** a universal
floating-point underflow guarantee: even a single prediction-emission
product can underflow. For example two positive representable factors
$10^{-200}$ have real product $10^{-400}$, below positive binary64 range.
Log-domain evaluation or stronger numerical assumptions are separate concerns.

## Sources

- L. R. Rabiner, "A tutorial on hidden Markov models and selected applications in speech recognition", Proceedings of the IEEE 77 (1989), 257–286, <https://doi.org/10.1109/5.18626> (scaling). The identities are derived above.
