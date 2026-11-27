# Borel–Tanner outbreak size and extinction-time recursion of a lagged Poisson branching epidemic

**Setting.** In the [lagged Poisson branching epidemic](growth-rate-and-extinction-of-a-lagged-poisson-branching-epidemic.md) with delay means $\Psi_1,\dots,\Psi_d > 0$ and $R_\infty = \sum_l\Psi_l$, let $T_{\mathrm{ext}}$ be the extinction time, $G_n = \Pr(T_{\mathrm{ext}} \le n)$, and $N = \sum_{l=-(d-1)}^{T_{\mathrm{ext}}-1} I_l$ the total number of cases.

**Extinction time.** For every $R_\infty$ and $n \ge d$,

$$G_n = \mathbb{E}\Big[\exp\Big(-\sum_{l=0}^{d-1} I_{n-d-l}\sum_{h=l+1}^{d}\Psi_h\Big)\Big],$$

so $G_n$ decreases when any $\Psi_l$ increases. In the single-type case $d = 1$ with $I_0$ initial cases and mean $\Psi$,

$$G_n = \exp\big[-\Psi I_0\big(1 - G_{n-1}^{1/I_0}\big)\big],$$

an exact recursion; for $d > 1$ an analogous recursion holds through the iterates of the offspring generating function.

**Outbreak size.** If $R_\infty < 1$ and the epidemic starts from $I_0$ cases of age zero, $N$ has the Borel–Tanner distribution with parameters $(R_\infty, I_0)$:

$$\Pr(N = k) = \frac{I_0}{k}\,\frac{(kR_\infty)^{k-I_0}}{(k-I_0)!}\,e^{-kR_\infty}\quad (k \ge I_0),\qquad \mathbb{E}N = \frac{I_0}{1-R_\infty},\qquad \operatorname{Var}N = \frac{I_0R_\infty}{(1-R_\infty)^3}.$$

From a general initial vector $(I_0, I_{-1},\dots,I_{-(d-1)})$, each case of age $h-1$ contributes itself plus a $\mathrm{Poisson}(\sum_{l\ge h}\Psi_l)$ number of independent Borel–Tanner$(R_\infty, 1)$ trees, so

$$\mathbb{E}N = \sum_{h=1}^{d} I_{-(h-1)}\Big[\frac{\sum_{l=h}^{d}\Psi_l}{1-R_\infty} + 1\Big].$$

## Expansion

Given the history up to time $n-d$, the event $\{\tilde I_n = 0\}$ requires every case at times $n-2d+1,\dots,n-d$ to produce no offspring at the remaining delays, and Poisson thinning gives the exponential. For the outbreak size, ignoring timing, each case produces a $\mathrm{Poisson}(R_\infty)$ total number of children (a sum of independent Poissons over delays), so the genealogy is a Poisson Galton–Watson tree whose total progeny generating function solves $g(s) = s\,e^{-R_\infty(1-g(s))}$; Lagrange inversion gives the Borel–Tanner law, and the moments follow from $\mathbb{E}N = I_0\sum_k R_\infty^k$ and the corresponding variance identity.

## Depends on

- [Growth rate and extinction probability of a lagged Poisson branching epidemic](growth-rate-and-extinction-of-a-lagged-poisson-branching-epidemic.md)

## Proof depends on

- [Borel–Tanner law](../../../../Probability/branching-processes/total-progeny-and-the-hitting-time-theorem/nat-cast-mul-hitting-weight-poisson.md)
- [Mean total progeny equals $1/(1-m)$](../../../../Probability/branching-processes/total-progeny-and-the-hitting-time-theorem/mean-total-progeny-eq.md)

## Sources

- Jacob C, "Branching processes: their role in epidemiology", Int J Environ Res Public Health (2010), Section 5, Propositions 12–14, <https://doi.org/10.3390/ijerph7031204>, PMCID PMC2872325.
