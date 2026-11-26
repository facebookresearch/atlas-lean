# Wald ratio as a weighted average derivative under a nonlinear dose-response

**Setting.** Let $A$ be a continuous exposure, $Y$ an outcome, $Z$ a genetic variant (allele count) or score, and $U$ the unmeasured common causes of $A$ and $Y$. Write $Y(a)$ for potential outcomes, $h(a,u) = E\{Y(a) \mid U = u\}$ for the stratum-specific dose-response curve, $h'(a,u) = \partial_a h(a,u)$, and $h'(a) = E\{h'(a,U)\}$ for the population slope. Assume the instrumental-variable conditions: $U$ suffices to control confounding of $A$ and $Y$, $Z$ affects $Y$ only through $A$, $Z \perp U$, and $Z$ is associated with $A$. The Wald estimand, the quantity targeted by two-sample summary-data Mendelian randomization, is

$$

\beta_{IV} = \frac{\operatorname{cov}(Z,Y)}{\operatorname{cov}(Z,A)} = \frac{\gamma_Y}{\gamma_A}, \qquad \gamma_Y = \frac{\operatorname{cov}(Z,Y)}{\operatorname{var}(Z)},\ \ \gamma_A = \frac{\operatorname{cov}(Z,A)}{\operatorname{var}(Z)} .

$$

**Variant weight.** Define $g(a) = \operatorname{cov}\{Z, \mathbf{1}(A > a)\}$ and its stratum version $g(a,u) = \operatorname{cov}\{Z, \mathbf{1}(A > a) \mid U = u\}$. Under the instrumental-variable conditions alone,

$$

\operatorname{cov}(Z,Y) = \int h'(a)\, g(a)\, da + \int \operatorname{cov}_U\{h'(a,U), g(a,U)\}\, da, \qquad \operatorname{cov}(Z,A) = \int g(a)\, da .

$$

**Result 1 (weighted average derivative).** Under the instrumental-variable conditions and the *no unmeasured common effect modifier* condition $\int \operatorname{cov}_U\{h'(a,U), g(a,U)\}\, da = 0$,

$$

\beta_{IV} = \frac{\int h'(a)\, g(a)\, da}{\int g(a)\, da},

$$

with a weight $g$ that depends only on the joint law of $(Z,A)$. The condition holds, for any first stage, when the confounder does not modify the effect ($h(a,u) = h(a) + \nu(u)$), and, for any outcome model, under an additive exposure density $f(a \mid u,z) = c(a,u) + \Lambda(a,z)$. With a linear heterogeneous outcome $h(a,u) = \beta_0(u) + \beta_Y(u)a$,

$$

\beta_{IV} - E\{\beta_Y(U)\} = \frac{\operatorname{cov}_U\{\beta_Y(U), \gamma_A(U)\}}{E\{\gamma_A(U)\}}, \qquad \gamma_A(u) = \frac{\operatorname{cov}(A, Z \mid U = u)}{\operatorname{var}(Z)},

$$

so the condition gives $\beta_{IV}$ equal to the average causal effect.

**Result 3 (nonnegative weights).** $g(a) = \operatorname{cov}\{Z, S(a \mid Z)\}$ with $S(a \mid z) = P(A > a \mid Z = z)$, so $g(a) \ge 0$ for every $a$ whenever $z \mapsto S(a \mid z)$ is nondecreasing for every $a$, i.e. the exposure distributions at different genotypes do not cross (first-order stochastic dominance). If $S(a_0 \mid \cdot)$ is not monotone, some instrument distribution makes $g(a_0) < 0$. Without non-crossing, the ratio need not lie in the range of the slope $h'$.

**Control-function version (Result 2).** If there is $T = T(A,Z)$ with $Y(a) \perp (A,Z) \mid T$, $T \perp Z$, $A = \kappa(T,Z)$ ($\kappa$ differentiable in $z$) and common support, then with $m(a,t) = E(Y \mid A = a, T = t)$, $w(z) = \operatorname{cov}\{Z, \mathbf{1}(Z > z)\} \ge 0$ and $f_Z$ the density of $Z$,

$$

\beta_{IV} = \frac{E\{\omega(Z,T)\, \partial_a m(A,T)\}}{E\{\omega(Z,T)\}}, \qquad \omega(z,t) = \frac{\partial \kappa(t,z)}{\partial z}\, \frac{w(z)}{f_Z(z)} .

$$

## Expansion

The decomposition follows from $\operatorname{cov}(Z,Y) = E[(Z - \bar z)\, h(A,U)]$: conditioning on $U = u$ and using $Z \perp U$, the inner term is $\int h(a,u) M(a,u)\, da$ with $M(a,u) = \operatorname{cov}\{Z, f(a \mid u, Z)\} = -\partial_a g(a,u)$, and integrating by parts gives $\int h'(a,u)\, g(a,u)\, da$; averaging over $U$ and splitting $E_U\{h' g\} = h' E_U\{g\} + \operatorname{cov}_U\{h', g\}$ yields the two terms, and $h(a,u) \equiv a$ gives the denominator. The weight is the continuous-exposure analogue of the Angrist–Imbens average causal response weight. Each variant has its own weight: a variant acting only at low doses averages the slope over low doses, and a variance-altering variant (location–scale first stage) has $g$ negative below a crossing dose and positive above it, so its ratio can lie outside the range of every individual effect. Consequently pooled estimators combine ratios with different estimands, and heterogeneity among per-variant ratios can arise from nonlinearity alone, with all instruments valid.

## Depends on

- [Ratio estimate of a single SNP](ratio-estimate.md)

## Sources

- Eric J. Tchetgen Tchetgen, "What does two-sample Mendelian randomization estimate when the exposure-outcome relationship is nonlinear?," arXiv 2026. Section 2 (Wald estimand), Section 3: Condition 1 (no unmeasured common effect modifier), Result 1, Result 2, Result 3; Appendices A, B and G. <https://doi.org/10.48550/arXiv.2610.05134>
