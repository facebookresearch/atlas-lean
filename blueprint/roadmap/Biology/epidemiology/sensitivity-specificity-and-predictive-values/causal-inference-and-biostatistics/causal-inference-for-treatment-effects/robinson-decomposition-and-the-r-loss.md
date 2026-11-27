# Robinson decomposition and the R-loss for the conditional average treatment effect

Observe i.i.d. triples $(X_i, Y_i, W_i)$, $i = 1, \dots, n$, with features $X_i \in \mathcal{X}$, outcome $Y_i \in \mathbb{R}$ and binary treatment $W_i \in \{0, 1\}$. Posit potential outcomes $\{Y_i(0), Y_i(1)\}$ with $Y_i = Y_i(W_i)$ and assume **unconfoundedness** $\{Y_i(0), Y_i(1)\} \perp W_i \mid X_i$ (Assumption 1 of the source). Write

- $\tau^*(x) = E\{Y(1) - Y(0) \mid X = x\}$, the conditional average treatment effect (CATE);
- $e^*(x) = \Pr(W = 1 \mid X = x)$, the propensity score;
- $\mu^*_{(w)}(x) = E\{Y(w) \mid X = x\}$ and $m^*(x) = E(Y \mid X = x) = \mu^*_{(0)}(x) + e^*(x)\tau^*(x)$.

**Robinson decomposition (eq. 1).** With $\varepsilon_i = Y_i - \{\mu^*_{(0)}(X_i) + W_i\tau^*(X_i)\}$, which satisfies $E(\varepsilon_i \mid X_i, W_i) = 0$,

$$Y_i - m^*(X_i) = \{W_i - e^*(X_i)\}\,\tau^*(X_i) + \varepsilon_i .$$

**R-loss characterization (eq. 2).** Assume $E(Y^2) < \infty$ and take $\tau$ over square-integrable functions of $X$. Consequently $\tau^*$ is a minimizer of

$$L(\tau), \qquad L(\tau) = E\Big[\big[\{Y_i - m^*(X_i)\} - \{W_i - e^*(X_i)\}\tau(X_i)\big]^2\Big],$$

and the regret is a propensity-weighted squared error:

$$R(\tau) := L(\tau) - L(\tau^*) = E\big[\{\tau(X_i) - \tau^*(X_i)\}^2\{W_i - e^*(X_i)\}^2\big].$$

Without overlap $\tau^*$ need not be the only minimizer: on a region where $e^*(X) \in \{0, 1\}$, $\{W - e^*(X)\}^2 = 0$ almost surely and changing $\tau$ there costs nothing. Under **overlap**, $\eta < e^*(x) < 1 - \eta$ for all $x$ and some $\eta > 0$, $\tau^*$ is the unique minimizer up to $P_X$-null sets, and regret and mean squared error are equivalent up to constants (eq. 12):

$$(1-\eta)^{-2} R(\tau) \le E[\{\tau(X_i) - \tau^*(X_i)\}^2] \le \eta^{-2} R(\tau),$$

with equality throughout at $\tau = \tau^*$, where all three quantities vanish.

**R-learner (eq. 4).** Split the sample into $Q$ folds with fold map $q(\cdot)$, fit $\hat m$ and $\hat e$ by cross-fitting (predictions $\hat m^{(-q(i))}, \hat e^{(-q(i))}$ never use unit $i$'s fold), and set

$$\hat\tau(\cdot) = \arg\min_\tau \Big[\frac1n\sum_{i=1}^n \big[\{Y_i - \hat m^{(-q(i))}(X_i)\} - \{W_i - \hat e^{(-q(i))}(X_i)\}\tau(X_i)\big]^2 + \Lambda_n\{\tau(\cdot)\}\Big],$$

where $\Lambda_n$ is a regularizer on the complexity of $\tau$.

## Expansion

Under unconfoundedness, $E\{Y - m^*(X) \mid X, W\} = \tau^*(X)\{W - e^*(X)\}$, so expanding the square gives $L(\tau) = E[\operatorname{var}\{Y - m^*(X) \mid X, W\}] + E[\{\tau(X) - \tau^*(X)\}^2\{W - e^*(X)\}^2]$; the first term does not depend on $\tau$. Since $\{W - e^*(X)\}^2$ lies between $\eta^2$ and $(1-\eta)^2$ when $W \in \{0,1\}$ and overlap holds, the two-sided bound follows. The residualization on both $Y$ and $W$ is what makes the loss locally insensitive to first-order errors in $\hat m$ and $\hat e$, the basis for the [quasi-oracle regret bound](r-learner-quasi-oracle-regret-bound.md).

## Sources

- X. Nie and S. Wager, *Quasi-oracle estimation of heterogeneous treatment effects*, Biometrika (2021). <https://doi.org/10.1093/biomet/asaa076>
- P. M. Robinson, *Root-N-consistent semiparametric regression*, Econometrica 56 (1988), 931-954. <https://doi.org/10.2307/1912705>
