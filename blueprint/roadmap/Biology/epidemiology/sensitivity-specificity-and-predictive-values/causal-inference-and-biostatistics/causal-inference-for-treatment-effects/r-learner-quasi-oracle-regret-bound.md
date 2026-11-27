# Quasi-oracle regret bound for the kernel R-learner

Work in the setting of the [Robinson decomposition and R-loss](robinson-decomposition-and-the-r-loss.md) with unconfoundedness and overlap $\eta < e^*(x) < 1 - \eta$. Let $K$ be a kernel on $\mathcal{X}$ with $K(x,x) \le 1$, Mercer eigenvalues $\sigma_j$ and eigenfunctions $\psi_j$, and RKHS $\mathcal{H}$. Assume (Assumptions 2-3 of the source):

- $\sup_j j^{1/p}\sigma_j < \infty$ for some $0 < p < 1$, $\sup_j \|\psi_j\|_\infty < \infty$, and $|Y_i| \le M$ almost surely;
- $\|T_K^{\alpha}\{\tau^*(\cdot)\}\|_{\mathcal{H}} < \infty$ for some $0 < \alpha < 1/2$, where $T_K$ is the kernel integral operator.

The **oracle** learner $\tilde\tau$ minimizes $n^{-1}\sum_i[\{Y_i - m^*(X_i)\} - \{W_i - e^*(X_i)\}\tau(X_i)]^2 + \Lambda_n(\|\tau\|_{\mathcal{H}})$ over $\|\tau\|_\infty \le 2M$ (eq. 10); the **feasible** R-learner $\hat\tau$ replaces $m^*, e^*$ by cross-fitted estimates (eq. 11). The best oracle bound is $R(\tilde\tau) = \tilde O_P\big(n^{-(1-2\alpha)/\{p + (1-2\alpha)\}}\big)$ (eq. 13).

**Theorem (Theorem 3 of the source, with Lemma 2).** Suppose in addition that

- $\sup_{x}|\hat e(x) - e^*(x)| \to 0$ in probability, and
- $E[\{\hat m(X) - m^*(X)\}^2]$ and $E[\{\hat e(X) - e^*(X)\}^2]$ are $O(a_n^2)$ with $a_n = O(n^{-\kappa})$ for some $\kappa > 1/4$,

and that $2\alpha < 1 - p$. Then, for a suitably chosen penalty $\Lambda_n(\|\tau\|_{\mathcal{H}})$, the feasible kernel R-learner satisfies the same regret bound as the oracle:

$$R(\hat\tau) = \tilde O_P\big(n^{-(1-2\alpha)/\{p + (1-2\alpha)\}}\big),$$

where $\tilde O_P$ hides logarithmic factors. By the overlap equivalence, the same rate holds for $E[\{\hat\tau(X) - \tau^*(X)\}^2]$.

## Expansion

The oracle rate comes from a quasi-isomorphic coordinate projection argument (Bartlett; Mendelson and Neeman) relating empirical and population $c$-regret over capped RKHS balls $\mathcal{H}_c$. Lemma 2 of the source shows that, with cross-fitting and nuisance errors $o(n^{-1/4})$, the feasible empirical regret differs from the oracle one by at most $0.125\,R(\tau; c) + o(\rho_n(c))$ uniformly over $\tau \in \mathcal{H}_c$, $1 \le c \le c_n\log n$; slightly more regularization then transfers any oracle regret bound to $\hat\tau$. The cross terms are second order because the R-loss is orthogonal to the nuisances. In the limit $\alpha, p \to 0$ this recovers the familiar fourth-root nuisance requirement for root-$n$ semiparametric inference. The source shows the X-learner lacks this property: $o(n^{-1/4})$ shifts of its outcome regressions shift its CATE estimate by the same amount.

## Depends on

- [Robinson decomposition and the R-loss](robinson-decomposition-and-the-r-loss.md)

## Sources

- X. Nie and S. Wager, *Quasi-oracle estimation of heterogeneous treatment effects*, Biometrika (2021). <https://doi.org/10.1093/biomet/asaa076>
