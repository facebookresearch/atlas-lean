# Log-rank tests of the Markov property in multi-state models

**Setting.** Subjects $i = 1, \dots, n$ follow a multi-state process $X_i(t)$ with finite state space, observed under independent right
censoring with at-risk indicator $Y_i(t)$; $N_i^{(lm)}(t)$ counts subject $i$'s observed $l \to m$ transitions, and
$Y_{il}(t) = \mathbf 1\{X_i(t-) = l\}\, Y_i(t)$. For a start time $s$ and state $j$, let $\delta_i^{(j)}(s) = \mathbf 1\{X_i(s) = j\}$. Under a Markov
process the intensity $\alpha_{lm}(t)$ for $t > s$ does not depend on whether the subject was in state $j$ at time $s$:

$$H_0:\ \alpha_{lm}(t \mid X(s) = j) = \alpha_{lm}(t \mid X(s) \ne j), \qquad t \ge s .$$

**Local test.** For each transition $l \to m$ with $l$ reachable both from $j$ and from some other state, the log-rank statistic comparing
the groups $\{X_i(s) = j\}$ and $\{X_i(s) \ne j\}$ among subjects under observation at $s$ is

$$U_s^{(j)}(l,m) = \sum_{i=1}^n \int_s^\tau \Bigl( \delta_i^{(j)}(s) - \frac{\sum_k \delta_k^{(j)}(s) Y_{kl}(t)}{\sum_k Y_{kl}(t)} \Bigr) dN_i^{(lm)}(t),$$

with variance estimate, summing over the distinct $l\to m$ transition times $t_{(k)} \ge s$,

$$\widehat{\operatorname{Var}}\bigl(U_s^{(j)}\bigr) = \sum_{k :\, t_{(k)} \ge s} \frac{n_{k1}(n_k - n_{k1})}{n_k^2}, \qquad n_k = \sum_i Y_{il}(t_{(k)}),\quad n_{k1} = \sum_i Y_{il}(t_{(k)})\delta_i^{(j)}(s).$$

Under $H_0$ the standardized $\bar U_s^{(j)}(l,m) = U_s^{(j)}(l,m)/\widehat{\operatorname{Var}}^{1/2}$ is asymptotically $N(0,1)$, and statistics for distinct
transitions are asymptotically independent, so $\sum_{(l,m)} \bar U_s^{(j)}(l,m)^2$ is asymptotically $\chi^2$ with as many degrees of freedom
as transitions.

**Global test.** For $s \le s'$ the covariance is estimated by

$$\widehat{\operatorname{Cov}}\bigl(U_s^{(j)}, U_{s'}^{(j)}\bigr) = \sum_{k:\, t_{(k)} \ge s'} \frac{n_k^{11} n_k^{00} - n_k^{01} n_k^{10}}{n_k^2},$$

where $n_k^{ab}$ counts subjects at risk at $t_{(k)}$ with $\delta^{(j)}(s) = a$ and $\delta^{(j)}(s') = b$. Under $H_0$ for all $s \in [t_0, t_{\max}]$, the
process $\{\bar U_s^{(j)}(l,m)\}_{s}$ converges to a mean-zero Gaussian process with covariance
$\operatorname{Cov}(U_s, U_{s'})/\sqrt{\operatorname{Var}(U_s)\operatorname{Var}(U_{s'})}$, which calibrates the global statistics
$\sup_{s\in[t_0,t_{\max}]} |\bar U_s^{(j)}(l,m)|$ and $\int_{t_0}^{t_{\max}} w(s)\,|\bar U_s^{(j)}(l,m)|\,ds$.

## Expansion

If the process is Markov, past occupancy of state $j$ carries no information about future intensities given the current state, so the two
groups share $\alpha_{lm}$ after $s$ and the log-rank comparison is a standard two-sample test with counting-process martingale structure.
A rejection also indicates that the Aalen–Johansen estimator of $P_j(s,t)$, which pools both groups, may be inconsistent, whereas the
landmark Aalen–Johansen estimator using only subjects in $j$ at $s$ is not. (Titman and Putter 2020, Equations 3.1–3.3 and
Sections 3.1–3.3.)

## Sources

- A. C. Titman and H. Putter, "General tests of the Markov property in multi-state models", Biostatistics (2020), <https://doi.org/10.1093/biostatistics/kxaa030>.
