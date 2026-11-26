# Lee–Huang–Yang error exponent

Use $\eta = 1/1615$ in the error power $(\rho a^3)^{1/2 + \eta}$ in the Lee–Huang–Yang
lower bound (Theorem 1.2), where $\rho$ is the density and $a$ is the scattering length.
This is one admissible universal exponent, not a value stated in Theorem 1.2 or an
optimality claim.

With $t = \rho_\mu a^3$, equation (5.27) of Fournais and Solovej sets $X = t^{1/323}$.
After factoring out $t^{1/2}$ in (6.30), the remaining error terms are proportional to
$X^2$, $t^{1/2}$, and $X^{1/5}$. For $0 < t \le 1$, both $X^2$ and $t^{1/2}$ are at most
$X^{1/5} = t^{1/1615}$. The proof of Theorem 1.2 sets $\rho_\mu = \rho$ in (4.4), which
preserves the exponent.

## Sources

- S. Fournais and J. P. Solovej, *The energy of dilute Bose gases*, Annals of Math. 192 (3), 2020, Theorems 1.2 and 6.8 and equations (4.4), (5.27), and (6.30).
- The declaration name and type are adapted from [AnnalsChallenge](https://github.com/ImperialCollegeLondon/AnnalsChallenge), problem `annals_bose_gases` in the lean-eval benchmark.
