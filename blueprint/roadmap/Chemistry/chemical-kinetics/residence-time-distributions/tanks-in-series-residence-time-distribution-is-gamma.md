# The residence-time distribution of tanks in series is a gamma distribution

Let $n$ be a positive integer and $\tau > 0$. The residence-time density of $n$ equal stirred tanks in
series with total residence time $\tau$,

$$p(\theta) = \left(\frac{n}{\tau}\right)^{n} \frac{\theta^{\,n-1}}{(n-1)!} \, e^{-n\theta/\tau}
\ (\theta \ge 0), \qquad p(\theta) = 0 \ (\theta < 0),$$

is the density of the gamma distribution with shape $n$ and rate $n/\tau$. Hence a residence time
$T_n$ with this distribution has the distribution function

$$P(T_n \le \theta) = \frac{\gamma(n, n\theta/\tau)}{\Gamma(n)} \quad (\theta \ge 0), \qquad
\gamma(n, x) = \int_0^x t^{\,n-1} e^{-t} \, dt,$$

mean $\tau$ and variance $\tau^2/n$. For every tolerance $\varepsilon > 0$,

$$P(|T_n - \tau| \ge \varepsilon) \ \le\ \min\Bigl(1, \frac{\tau^2}{n \varepsilon^2}\Bigr),$$

and the bound tends to $0$ as $n \to \infty$ with $\tau$ and $\varepsilon$ fixed. For example,
$\tau = 1$, $n = 100$ and $\varepsilon = 1/2$ give the bound $1/25$; for $n = 1$ the law is the
exponential law of a single stirred tank. So the mean residence time does not depend on the number of
tanks, while the residence time concentrates at $\tau$, the plug-flow value, as the number of tanks
grows.

Changing the time unit by a factor $c > 0$ is consistent with all of this: $c\,T_n$ has the gamma law
with shape $n$ and rate $n/(c\tau)$, so its mean is $c\tau$, its variance is $c^2\tau^2/n$, and the
event $|c\,T_n - c\tau| \ge c\varepsilon$ is the event $|T_n - \tau| \ge \varepsilon$, with the
same bound. A scale $c = 0$ is not a change of unit: it sends every residence time to $0$.

The density is the [bolus response of the tanks](tanks-in-series-bolus-response.md). The mean is
$n/(n/\tau)$ by the [mean of the gamma distribution](../../../Probability/distributions/continuous/gamma-distribution/gamma-moments/integral-id-gamma-measure.md) and the variance is
$n/(n/\tau)^2$ by the [variance of the gamma distribution](../../../Probability/distributions/continuous/gamma-distribution/gamma-moments/variance-id-gamma-measure.md). The tolerance bound is
[Chebyshev's inequality](../../../Probability/moments/chebyshev-s-inequality/meas-ge-le-variance-div-sq.md) for this variance, together with the trivial bound $1$ on a
probability. The change of unit is the [scaling of a gamma random variable](../../../Probability/distributions/continuous/gamma-distribution/gamma-scaling/gamma-measure-map-const-mul.md).

## Depends on

## Proof depends on

- [Bolus response of equal stirred tanks in series](tanks-in-series-bolus-response.md), identifying the density as the residence-time distribution
- [Mean of the gamma distribution](../../../Probability/distributions/continuous/gamma-distribution/gamma-moments/integral-id-gamma-measure.md)
- [Variance of the gamma distribution](../../../Probability/distributions/continuous/gamma-distribution/gamma-moments/variance-id-gamma-measure.md)
- [Chebyshev's inequality](../../../Probability/moments/chebyshev-s-inequality/meas-ge-le-variance-div-sq.md), for the tolerance bound
- [Scaling a gamma random variable](../../../Probability/distributions/continuous/gamma-distribution/gamma-scaling/gamma-measure-map-const-mul.md), for the change of time unit

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 8.2.5, Equations 8.16–8.18 (pp. 440–441), including the remark that the
  distribution becomes more narrowly focused at $\tau$ as $n$ increases.
