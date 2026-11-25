# Expected time to the first coalescence

For a real function $\eta$ and a natural number $m$, let

$$c_m(\eta) = \int_0^\infty \exp\Bigl(-\binom{m}{2} R_\eta(s)\Bigr)\, ds,$$

with the [cumulative coalescence intensity](cum-rate.md) $R_\eta$ and the convention that a non-integrable integrand has integral $0$; for instance $c_0(\eta) = c_1(\eta) = 0$, since the integrand is then the constant $1$. For a positive relative population size $\eta$ with $1/\eta$ locally integrable, $m \ge 2$ and an integrable integrand, $c_m$ is the expected time to the first coalescence among $m$ lineages; when the integrand is not integrable, as for $\eta(s) = e^{s}$ and $m = 2$, where the expected time is infinite, the value $0$ is only the convention. For a [piecewise-constant history](piecewise-history.md) with at least one piece and $m \ge 2$, the integrand is integrable ([closed form of the first-coalescence times](choose-two-mul-first-coal-mean.md)).

## Sources

- A. Bhaskar and Y. S. Song, *Descartes' rule of signs and the identifiability of population demographic models from genomic variation data*, Ann. Statist. 42 (2014), 2469–2493; arXiv:1309.5056.
