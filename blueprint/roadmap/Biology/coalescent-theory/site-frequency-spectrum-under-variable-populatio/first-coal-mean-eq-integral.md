# The expected first-coalescence time as a survival integral

For every real function $\eta$ and every natural number $m$,

$$c_m(\eta) = \int_{(0, \infty)} \exp\Bigl(-\binom{m}{2} R_\eta(s)\Bigr)\, ds,$$

where $c_m(\eta)$ is the [expected time to the first coalescence](first-coal-mean.md) among $m$
lineages and $R_\eta(s) = \int_0^s dr / \eta(r)$ is the
[cumulative coalescence intensity](cum-rate.md). The conventions are $1/0 = 0$ in $R_\eta$, and
that an integral of a non-integrable function is $0$, both in $R_\eta$ and in the integral over
$(0, \infty)$; for instance $c_0(\eta) = c_1(\eta) = 0$, since the integrand is then the constant
$1$. For a positive relative population size $\eta$ with $1/\eta$ locally integrable, the
integrand is the probability that none of the $\binom{m}{2}$ pairs of lineages has coalesced by
time $s$.
