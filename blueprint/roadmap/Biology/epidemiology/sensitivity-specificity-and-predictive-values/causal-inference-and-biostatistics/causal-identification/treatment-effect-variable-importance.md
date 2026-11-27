# Treatment-effect variable importance measures

Let $Z = (Y, A, X)$ with outcome $Y \in \mathbb R$, binary treatment $A$ and covariates $X \in \mathbb R^p$, and potential outcomes $Y^1, Y^0$. Assume consistency ($A = a \Rightarrow Y = Y^a$), conditional exchangeability ($Y^a \perp A \mid X$) and positivity ($0 < \pi(X) < 1$ a.s., $\pi(x) = P(A = 1 \mid X = x)$), with square-integrable outcomes. Then the CATE $\tau(x) = E(Y^1 - Y^0 \mid X = x) = \mu(1, x) - \mu(0, x)$, $\mu(a, x) = E(Y \mid A = a, X = x)$, is identified. For $s \subseteq \{1, \dots, p\}$ let $\tau_s(x) = E(Y^1 - Y^0 \mid X_{-s} = x_{-s}) = E\{\tau(X) \mid X_{-s} = x_{-s}\}$.

1. For every square-integrable $f$, the (unidentified) mean squared error of predicting the individual effect decomposes as

$$L\{f\} := E[\{Y^1 - Y^0 - f(X)\}^2] = E[\{\tau(X) - f(X)\}^2] + E\{\mathrm{var}(Y^1 - Y^0 \mid X)\},$$

and the second term does not depend on $f$.
2. The **TE-VIM** of $X_s$ is

$$\Theta_s := L\{\tau_s\} - L\{\tau\} = E[\{\tau(X) - \tau_s(X)\}^2] = \mathrm{var}\{\tau(X)\} - \mathrm{var}\{\tau_s(X)\} \ \ge 0,$$

which is identified; $\Theta_{\{1,\dots,p\}} = \mathrm{var}\{\tau(X)\}$ is the variance of the treatment effect, and, when $\mathrm{var}\{\tau(X)\} > 0$, $\Psi_s = \Theta_s / \mathrm{var}\{\tau(X)\} \in [0, 1]$ is the share of effect heterogeneity explained by $X_s$ beyond $X_{-s}$. The scaled measure $\Psi_s$ is undefined when the treatment effect is constant in $X$ (then $\Theta_s = \mathrm{var}\{\tau(X)\} = 0$); the unscaled $\Theta_s$ needs no such restriction.
3. With the doubly robust pseudo-outcome

$$\varphi(Z) = \frac{A - \pi(X)}{\pi(X)\{1 - \pi(X)\}}\bigl\{Y - \mu(A, X)\bigr\} + \mu(1, X) - \mu(0, X),$$

one has $E\{\varphi(Z) \mid X\} = \tau(X)$ and hence $E\{\varphi(Z) \mid X_{-s}\} = \tau_s(X)$, so $\tau$ and $\tau_s$ can be learned by regressing $\varphi$ (or $\hat\tau(X)$) on $X$ and $X_{-s}$.

## Expansion

(1) Write $Y^1 - Y^0 - f = (Y^1 - Y^0 - \tau) + (\tau - f)$; the cross term vanishes after conditioning on $X$. (2) Apply (1) with $f = \tau_s$ and $f = \tau$; since $\tau_s = E(\tau \mid X_{-s})$, $E[(\tau - \tau_s)\tau_s] = 0$, giving the variance difference. (3) Conditionally on $X$, $E[(A - \pi)(Y - \mu(A, X)) \mid X] = 0$ term by term in $A \in \{0, 1\}$, so only $\mu(1, X) - \mu(0, X)$ survives. The paper's Theorems 1 and 2 give conditions (sample splitting or Donsker, rate conditions on nuisance estimates) under which the efficient-influence-curve estimators of $\Theta_s$ and $\Psi_s$ are asymptotically linear.

## Sources

- O. Hines, K. Diaz-Ordaz and S. Vansteelandt, "Variable importance measures for heterogeneous treatment effects", *Biometrics* (2025), <https://doi.org/10.1093/biomtc/ujaf140> (PMC7618827). Section 1 (decomposition of $L\{f\}$ and definition of $\Theta_s$), Section 2 (identification, DR-learner identities, Theorems 1 and 2).
