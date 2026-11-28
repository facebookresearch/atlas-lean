# Rejection ABC returns the tolerance-conditioned posterior

Let $\mu$ be a prior probability measure on a standard Borel parameter
space and $P_\theta$ a probability kernel for simulated data.
Let $A_\varepsilon=\{x:d(S(x),s_{\rm obs})\le\varepsilon\}$ be measurable,
where $\varepsilon\ge0$ and the discrepancy from the observed summary
is measurable. Set $a_\varepsilon(\theta)=P_\theta(A_\varepsilon)$ and
assume $Z_\varepsilon=\int a_\varepsilon\,d\mu>0$.
Independently repeat prior draws and conditional simulations until the
first acceptance. That returned parameter has law

$$\pi_\varepsilon(d\theta)
 =Z_\varepsilon^{-1}a_\varepsilon(\theta)\mu(d\theta).$$

At infinite tolerance, when every simulated datum is accepted, this is
the prior. If $S$ takes countably many values, $d$ is a metric and
$\varepsilon=0$, it is exactly the posterior given
$S(X)=s_{\rm obs}$, provided that event has positive probability.
With a mere pseudometric, zero tolerance conditions on the entire
zero-distance class, not necessarily on one summary value.

For discrete data, the zero-tolerance posterior also equals the full-data
posterior at an observation of positive evidence if $S$ is sufficient.
Here sufficiency means that, conditional on $S(X)$, the distribution of
$X$ is independent of the parameter; equivalently for this Bayesian
statement, $\theta$ and $X$ are conditionally independent given $S(X)$.
This condition is part of the claim, not a property of arbitrary summaries.

## Depends on

- [Bayes' rule for discrete observations](../bayes-rule/posterior-eq-bayes-posterior.md)

## Background

- [Discrete rejection-round acceptance probability](tsum-trial-true.md)

## Expansion

For a measurable parameter set $B$, the probability a single attempt
accepts with parameter in $B$ is $\int_B a_\varepsilon\,d\mu$.
The probability of rejecting the first $n$ attempts is
$(1-Z_\varepsilon)^n$. Summing the geometric series proves the target
formula and almost-sure termination. This directly proves the general
kernel result; the linked PMF acceptance-probability theorem alone would
not establish the accepted law on a continuous parameter space.
Conditional independence under sufficiency makes the posterior given
full data equal the posterior given its summary. In the usual discrete
factorization $P_\theta(X=x)=g_\theta(S(x))h(x)$, both posteriors reweight
the prior by the same $g_\theta(s_{\rm obs})$, differing only by constants.

For an explicit failure without sufficiency, put equal prior mass at
$\theta=1/4,3/4$, observe two conditionally independent Bernoulli trials
$(1,1)$, and keep only $S(x)=x_1$. The posterior probability of $\theta=3/4$
is $3/4$ using the summary, but $9/10$ using both observations.
With continuous summaries a zero-tolerance event often has probability
zero, in which case this rejection procedure has no accepted law; a
limiting-tolerance theorem requires additional assumptions.

## Sources

- M. A. Beaumont, W. Zhang and D. J. Balding, *Approximate Bayesian computation in population genetics*, Genetics 162 (2002), 2025–2035, <https://doi.org/10.1093/genetics/162.4.2025>, bibliographic background only. The target law, sufficiency condition and finite counterexample are derived above.
