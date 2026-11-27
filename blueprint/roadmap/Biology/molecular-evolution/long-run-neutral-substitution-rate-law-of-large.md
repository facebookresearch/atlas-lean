# Long-run expected calendar-time rate of neutral substitution

Use the [neutral infinite-sites copying model](neutral-substitution-expected-eventual-fixer-ori.md)
with constant integer size $M\ge1$. Start at time zero with finitely many
segregating sites. Count mutation births in generations $1,\ldots,T$;
let $K_T$ count those already fixed by time $T$, plus initially segregating
sites that first fix in this interval. Already fixed initial sites are not
new substitutions. Then

$$\frac{\mathbb E K_T}{T}\longrightarrow u.$$

## Depends on

- [Neutral origination flux and finite absorption](neutral-substitution-expected-eventual-fixer-ori.md)

## Expansion

Let $A_T$ count eventual fixers born in generations $1,\ldots,T$, and
$B_T$ count those still segregating at $T$.
Then $K_T=A_T-B_T+I_T$, where $0\le I_T\le J_0$, the finite number
of initially segregating sites, and $\mathbb E A_T=uT$.
If $\tau$ is the absorption delay of a single newly born copy and $F$
is eventual fixation, stationarity of the single-site birth law gives

$$\mathbb E B_T=u\sum_{k=0}^{T-1}\mathbb P(\tau>k\mid F)
\le u\,\mathbb E[\tau\mid F]<\infty.$$

Indeed $\mathbb P(F)=1/M$ and the preceding geometric tail implies
$\mathbb P(\tau>k\mid F)\le M(1-M^{-M})^k$, so
$\mathbb E[\tau\mid F]\le M^{M+1}$ suffices.
For $M=1$, every mutation is fixed at birth and the delay is zero.
The bounded expectation of the backlog proves the limit. Independence
between sites' fates is not used. A large-population diffusion estimate
of a delay near $2M$ is not assumed as an exact finite-size identity.

The stronger almost-sure law $K_T/T\to u$ needs a separate renewal or
ergodic proof. A rare-mutation Poisson-process limit likewise needs its
own scaling and separation-of-timescales theorem. Neither follows from
this expectation calculation, and both remain residual objectives.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics*, University of Washington (2019 edition), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section VI.5, "Rate of substitution of alleles" (prospective and retrospective arguments for rate $u$).
