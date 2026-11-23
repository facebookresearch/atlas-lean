# Survival-integral form of the first-coalescence quantity $c_m$

For every real function $\eta$ and every natural number $m$,

$$c_m(\eta) = \int_{(0, \infty)} \exp\Bigl(-\binom{m}{2} R_\eta(s)\Bigr)\, ds,$$

where $c_m(\eta)$ is the quantity defined on the page
[expected time to the first coalescence](first-coal-mean.md) and
$R_\eta(s) = \int_0^s dr / \eta(r)$ is the [cumulative coalescence intensity](cum-rate.md). The
identity holds with no condition on $\eta$ or $m$, with the conventions $1/0 = 0$ in $R_\eta$ and
that an integral of a non-integrable function is $0$, both in $R_\eta$ and in the integral over
$(0, \infty)$; for instance $c_0(\eta) = c_1(\eta) = 0$, since the integrand is then the constant
$1$.

For a positive relative population size $\eta$ with $1/\eta$ locally integrable and $m \ge 2$, the
integrand at $s$ is the probability that none of the $\binom{m}{2}$ pairs of lineages has
coalesced by time $s$. The integral is the expected time to the first coalescence only when this
survival function is integrable: for $\eta(s) = e^{s}$ and $m = 2$ the survival probability tends
to $e^{-1}$, so the waiting time has infinite mean, while the formula gives $0$.
