# Speed of adaptation under beneficial mutation-selection balance

In the steady state of an asexual population of size $N$ with beneficial mutation rate $U_b$ and common
mutation effect $s$, the mean fitness and the nose of the fitness distribution both advance by $s$ in one
establishment interval, so the speed of evolution is

$$v = \frac{s}{\langle \tau_q \rangle}.$$

Substituting the mean establishment interval and the lowest-order solution for the steady-state lead
gives, in the concurrent-mutations regime,

$$v \approx s^2\,\frac{2\ln[Ns] - \ln[s/U_b]}{\ln^2[s/U_b]},$$

valid when the lead $q$ is reasonably large, which holds roughly when $2\ln[Ns] > \ln(s/U_b)$, that is
when $NU_b \gg 1$. The speed therefore grows only logarithmically in $N$ and in $U_b$, in contrast with
the linear dependence $v = NU_b s^2$ of the successional regime. For $NU_b \ll 1$ the two regimes are
joined by

$$v \approx \frac{s^2}{\ln Ns + 1/(NU_b)},$$

which reduces to $NU_b s^2$ when $NU_b \ln[Ns] \ll 1$ and to the $q = 2$ result $s^2/\ln[Ns]$ when
$NU_b \gtrsim 1$.

This is consistent with the fundamental theorem of natural selection. The bulk of the fitness
distribution is Gaussian with variance $\sigma^2$, since a class $\ell$ steps from the mean grows or
shrinks like $e^{\ell s t}$ while the mean advances one step per interval; the most-fit established
class, at $\ell \approx q$, then has size of order $N\sigma \exp[-(qs)^2/(2\sigma^2)]$ of order one, which
gives $v = \sigma^2$ with the $\sigma^2$ implied by the formula above. The analysis never uses the
variance as an input: the lead, not the variance, is the quantity set by the balance between mutation at
the nose and selection in the bulk.

## Depends on

- [Steady-state lead of the fitness distribution under beneficial mutation-selection balance](steady-state-lead-of-the-fitness-distribution.md)
- [Establishment interval at the nose of the fitness distribution](establishment-interval-at-the-nose.md)
- [Clonal interference](clonal-interference.md)

## Proof depends on

- [Steady-state lead of the fitness distribution under beneficial mutation-selection balance](steady-state-lead-of-the-fitness-distribution.md)
- [Establishment interval at the nose of the fitness distribution](establishment-interval-at-the-nose.md)

## Expansion

Once the class at lead $qs$ establishes, the situation repeats with the nose advanced by one mutation and
the mean advanced by $s$, so $s/\langle\tau_q\rangle$ is the steady-state rate. The logarithmic
dependence on $N$ has a mechanistic reading: almost all beneficial mutations occur far from the nose, in
backgrounds doomed to extinction, so enlarging $N$ does not enlarge the useful supply of mutations.
Instead it lengthens the time selection needs to move the mean, which widens the lead, which makes the
individuals at the nose fitter relative to the mean and speeds their establishment. Raising $U_b$ acts
the same way, by shortening the time for new mutations to appear at the nose. Simulations across ranges
of $N$, $U_b$ and $s$ match these predictions, with the theory slightly underestimating both $v$ and $q$.

## Sources

- M. M. Desai and D. S. Fisher, "Beneficial mutation-selection balance and the effect of linkage on positive selection", Genetics 176 (2007), 1759-1798, <https://doi.org/10.1534/genetics.106.067678> (PMC1931526). (Equations 38, 41 and 47.)
