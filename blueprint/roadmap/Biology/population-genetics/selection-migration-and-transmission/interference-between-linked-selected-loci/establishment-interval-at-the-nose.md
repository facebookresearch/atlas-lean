# Establishment interval at the nose of the fitness distribution

Work in the concurrent-mutations regime of an asexual population of size $N$ with beneficial mutation
rate $U_b$, mutations of common effect $s$, and steady-state lead $qs$ with $q > 2$. Let $n_{q-1}$ be the
most-fit established class, growing exponentially at rate $(q-1)s$ from its establishment size
$1/\bigl[(q-1)s\bigr]$, and let $\tau_q$ be the interval until the next class $n_q$, one mutation fitter,
becomes established, where establishment time is defined by extrapolating the later deterministic growth
at rate $qs$ back to size $1/(qs)$. Then the mean and variance of this interval are

$$\langle \tau_q \rangle = \frac{1}{(q-1)s}\,
\ln\Bigl[\frac{s}{U_b}\,\frac{(q-1)\sin(\pi/q)}{\pi e^{\gamma/q}}\Bigr],
\qquad
\mathrm{Var}(\tau_q) = \frac{\pi^2}{6}\Bigl[\frac{1}{[(q-1)s]^2} - \frac{1}{[qs]^2}\Bigr],$$

where $\gamma = 0.5772\ldots$ is Euler's constant. The distribution of $\tau_q$ is skewed: values well
below the mean occur with appreciable probability, values well above it almost never.

## Depends on

- [Successional and concurrent regimes of beneficial mutations in an asexual population](successional-and-concurrent-mutation-regimes.md)

## Proof depends on

- [Successional and concurrent regimes of beneficial mutations in an asexual population](successional-and-concurrent-mutation-regimes.md)
- [Euler's gamma integral](../../../../Probability/distributions/continuous/gamma-distribution/gamma-moments/lintegral-rpow-mul-exp-neg-mul-ioi.md)

## Expansion

The feeding class $n_{q-1}(t)$ grows deterministically at rate $(q-1)s$ and throws off mutants at rate
$U_b n_{q-1}(t)$; each mutant founds a stochastic lineage that grows on average at rate $qs$ and may die
out. Writing the generating function of the fed population and passing to the Laplace variable
$\zeta = 1 - z$ gives a closed transform for the law of $n_q(t)$, from which $\langle \ln^m n_q(t)\rangle$
follows by differentiation; the Gamma function enters through that integral, and its expansion supplies
the Euler constant in the mean and the $\pi^2/6$ in the variance. Converting from $\ln n_q$ to $\tau_q$
with the definition of the establishment time gives the displayed expressions. The quantity is not simply
the waiting time for the first successful mutant: of order $q$ distinct mutational origins contribute
appreciably to the new most-fit class, and the formula accounts both for the randomness in their timing
and for the fluctuations of their early growth. The restriction $q > 2$ is needed because for smaller
leads the feeding class saturates while the fed class is still establishing.

## Sources

- M. M. Desai and D. S. Fisher, "Beneficial mutation-selection balance and the effect of linkage on positive selection", Genetics 176 (2007), 1759-1798, <https://doi.org/10.1534/genetics.106.067678> (PMC1931526). (Equations 36 and 37.)
