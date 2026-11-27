# The PPSZ round

For a CNF formula $\varphi$ and a bound $s$, one **PPSZ round** draws a uniformly random ordering of the variables and processes them in order, setting each variable to its $s$-implied value under the current partial assignment when it has one, and to a uniformly random bit otherwise. It succeeds if the resulting assignment satisfies $\varphi$. With $s = 1$ this is the PPZ round.

## Depends on

- [Bounded-width implication (s-implication)](bounded-width-implication.md)
- [Forced values and the PPZ round](ppz-forced-values-and-round.md)

## Sources

- R. Paturi, P. Pudlák, M. E. Saks and F. Zane, "An Improved Exponential-Time Algorithm for k-SAT", Journal of the ACM 52(3), 2005.
