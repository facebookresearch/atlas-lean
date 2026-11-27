# Speed limit of the neutral clock under uniform birth rates

Use the replacement model of [site fixation probabilities](site-fixation-probabilities-and-the-neutral-substitution-rate.md), with $N$ sites, replacement probabilities $e_{ij}$, birth rates $b_i$, death rates $d_i$ and neutral substitution rate $K = Nu\rho$.

**Theorem (uniform birth rates).** If $b_i$ is the same for all sites, then $\rho \le 1/N$ and hence $K \le u$, with equality if and only if the death rates $d_i$ are also constant across sites.

**Theorem (unconstrained structure).** With no restriction on $(e_{ij})$, the overall fixation probability $\rho$ can take any value in $[0,1)$, and so $K$ can take any value in $[0, Nu)$.

**Two-deme example.** Take an upstream deme of $N_\uparrow$ sites and a downstream deme of $N_\downarrow$ sites, each well mixed (replacement probabilities $e_\uparrow$ within upstream, $e_\downarrow$ within downstream), with $e_\to$ from each upstream site to each downstream site and $e_\leftarrow$ in the reverse direction. Then

$$\rho_\uparrow = \frac{e_\to}{N_\uparrow e_\to + N_\downarrow e_\leftarrow}, \qquad \rho_\downarrow = \frac{e_\leftarrow}{N_\uparrow e_\to + N_\downarrow e_\leftarrow},$$

$$K = \frac{N}{B}\,\frac{N_\uparrow d_\uparrow e_\to + N_\downarrow d_\downarrow e_\leftarrow}{N_\uparrow e_\to + N_\downarrow e_\leftarrow}\,u, \qquad B = N_\uparrow d_\uparrow + N_\downarrow d_\downarrow ,$$

where $d_\uparrow, d_\downarrow$ are the turnover rates of the two demes. With net downstream flow ($e_\to > e_\leftarrow$), $K > u$ if and only if $d_\uparrow > d_\downarrow$. With unidirectional flow ($e_\leftarrow = 0$), $K = (d_\uparrow/B)Nu$, which ranges over $[0, (N/N_\uparrow)u)$.

## Depends on

- [Site fixation probabilities and the neutral substitution rate](site-fixation-probabilities-and-the-neutral-substitution-rate.md)
- [Invariance of the neutral clock under uniform turnover or local birth-death balance](invariance-of-the-neutral-clock-under-uniform-turnover-or-local-balance.md)

## Expansion

The two-deme formulas follow by checking that the stated $\rho_\uparrow, \rho_\downarrow$ satisfy the balance equations and $N_\uparrow\rho_\uparrow + N_\downarrow\rho_\downarrow = 1$, then substituting into $K = (Nu/B)\sum_i d_i\rho_i$. With $e_\leftarrow = 0$ only upstream mutations can fix and each has $\rho_\uparrow = 1/N_\uparrow$; letting a single hub ($N_\uparrow = 1$) seed many downstream sites while carrying almost all turnover pushes $\rho$ toward $1$, which realizes the unconstrained range. Under uniform birth rates, the sites that receive most mutations are the high-turnover sites, which are replaced often and so hold low reproductive value; the formal proof that this negative association always gives $\rho \le 1/N$ is more involved than the intuition. As applications, a cycle of about five intestinal stem cells each replaced about $0.1$ times per day gives $\tilde K = 0.1u$ per day, whereas a well-mixed crypt of about $250$ cells each replaced once per day would give $\tilde K \approx u$, so crypt architecture slows the clock about tenfold.

## Sources

- B. Allen, C. Sample, Y. Dementieva, R. C. Medeiros, C. Paoletti and M. A. Nowak, "The molecular clock of neutral evolution can be accelerated or slowed by asymmetric spatial structure", PLoS Computational Biology 11 (2015), e1004108, Results 3 and 4, Eqs. (5)–(6) and Methods, <https://doi.org/10.1371/journal.pcbi.1004108>, PMCID PMC4342344.
