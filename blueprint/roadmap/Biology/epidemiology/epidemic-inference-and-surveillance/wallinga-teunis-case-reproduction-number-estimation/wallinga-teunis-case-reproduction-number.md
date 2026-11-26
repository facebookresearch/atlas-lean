# Wallinga–Teunis case reproduction number

**Setting.** A line list contains cases $i = 1, \dots, n$ with infection (or symptom-onset) times $t_i$, and $w$ is the generation-interval (or serial-interval) density, supported on $(0, \infty)$, with mean $\bar T$ and distribution function $W$. For a case $i$ with $Z_i = \sum_{k \ne i} w(t_i - t_k) > 0$, the relative likelihood that case $j$ infected case $i$ is

$$p_{ij} = \frac{w(t_i - t_j)}{Z_i}, \qquad j \ne i .$$

The individual reproduction number of case $j$ is $R_j = \sum_{i \ne j} p_{ij}$ (sum over cases with $Z_i > 0$), and the case reproduction number $R^{\mathrm{case}}(t)$ is the average of $R_j$ over cases with $t_j = t$. Its population counterpart, for a bounded instantaneous reproduction number $R^{\mathrm{inst}}$ (for an SIR or SEIR model, $R^{\mathrm{inst}}(t) = \beta(t) S(t) D$ with $D$ the mean infectious duration), is

$$R^{\mathrm{case}}(t) = \int_0^\infty R^{\mathrm{inst}}(t + s)\, w(s)\, ds .$$

**Proposition.**

1. (Conservation) For each case $i$ with $Z_i > 0$, $\sum_{j \ne i} p_{ij} = 1$, hence

$$\sum_{j=1}^n R_j = \#\{i : Z_i > 0\} \le n :$$

every case with a possible infector in the data is attributed exactly once, split among its candidate infectors.
2. (Forward dependence) $p_{ij} > 0$ only if $t_j < t_i$, so $R_j$ depends only on cases after $t_j$. For a list right-truncated at $T_{\mathrm{obs}}$, $R_j$ is biased downwards for $t_j$ within the support of $w$ before $T_{\mathrm{obs}}$ unless corrected for unobserved future cases.
3. (Posterior interpretation) If each case was infected by exactly one earlier case in the list, with infection times following $w$ after the infector's infection, and candidate infectors are a priori equally likely, then $p_{ij}$ is the posterior probability that $j$ infected $i$ given the times.
4. (Leading indicator) If $R^{\mathrm{inst}}$ jumps from $R_1$ to $R_2$ at time $t_0$, then $R^{\mathrm{case}}(t) = R_1 W(t_0 - t) + R_2(1 - W(t_0 - t))$ for $t < t_0$: the case reproduction number starts moving before the change.
5. (Mean-shift rule) If $R^{\mathrm{inst}}$ is affine on $[t, \infty)$, $R^{\mathrm{case}}(t) = R^{\mathrm{inst}}(t + \bar T)$; if it is twice differentiable with $|{R^{\mathrm{inst}}}''| \le M$, the error of this rule is at most $\tfrac{M}{2}\mathrm{Var}(w)$.

## Depends on

- [Reproductive number from growth rate and generation interval](../../euler-lotka-equation-and-the-reproduction-number/reproduction-number.md)

## Expansion

(1): for fixed $i$ the $p_{ij}$ are normalized weights; exchange the order of summation. (2) is the support condition on $w$. (3): the likelihood that the infector was $j$ is proportional to $w(t_i - t_j)$, which normalizes to $p_{ij}$. (4) splits the integral at $s = t_0 - t$. (5): for $R^{\mathrm{inst}}(t + s) = A + Bs$ the integral is $A + B\bar T$; otherwise Taylor's theorem about $s = \bar T$ leaves a remainder at most $\tfrac{M}{2}\int (s - \bar T)^2 w(s)\, ds$. Shifting the case number back by $\bar T$ therefore makes it comparable with real-time estimates of the instantaneous number. The weights can be modified with contact-tracing data on observed transmission pairs, or by an age-structured contact matrix to give age-specific estimates. Like the instantaneous estimators of Cori et al. and of Bettencourt and Ribeiro, the method assumes that all infections are observed. The Bettencourt–Ribeiro update $I_{t+1} = I_t \exp((R_t - 1)/g)$ is the Euler–Lotka relation $R = 1 + rg$ for an exponential generation interval of mean $g$, and is biased when the true interval is not exponential.

## Sources

- K. M. Gostic, L. McGough, E. B. Baskerville, S. Abbott, K. Joshi, C. Tedijanto, et al., "Practical considerations for measuring the effective reproductive number, $R_t$", PLoS Computational Biology 16 (2020) e1008409, Eqs. (1)–(6), <https://doi.org/10.1371/journal.pcbi.1008409> (PMC7728287).
- J. Wallinga, P. Teunis, "Different epidemic curves for severe acute respiratory syndrome reveal similar impacts of control measures", American Journal of Epidemiology 160 (2004) 509–516, <https://doi.org/10.1093/aje/kwh255>.
