# Counterfactual density and its projection onto a model by a moment condition

Observe i.i.d. $Z = (X, A, Y) \sim P$ with covariates $X \in \mathbb{R}^d$, discrete treatment $A$ and continuous outcome $Y \in \mathbb{R}$. Write $\pi_a(x) = P(A = a \mid X = x)$ and $\eta_a(y \mid x)$ for the conditional density of $Y$ given $X = x, A = a$ (eqs. 1-2). The covariate-adjusted marginal density (eq. 3) is

$$p_a(y) = \int \eta_a(y \mid x)\,dP(x).$$

**Identification.** Under positivity $P\{\pi_a(X) \ge \epsilon\} = 1$ for some $\epsilon > 0$, consistency ($Y = Y^a$ if $A = a$) and exchangeability $A \perp Y^a \mid X$ (Assumptions 1-3), $p_a$ is the density of the counterfactual outcome $Y^a$. It differs in general from both the marginal density of $Y$ and $p(y \mid a)$.

**Projection parameter (eq. 6).** For a model $\{g(y;\beta) : \beta \in \mathbb{R}^k\}$ and a distance $D_f(p, q) = \int f\{p(y), q(y)\}\,q(y)\,dy$,

$$\beta_0 = \arg\min_\beta D_f\{p_a(y), g(y;\beta)\},$$

which is well defined whether or not the model is correct.

**Proposition 1.** Assume $g$ is differentiable in $\beta$, $f$ is differentiable in its second argument with derivative $f_2'$, and the minimizer is unique. Then $\beta_0$ solves $m(\beta) = 0$, where

$$m(\beta) = \int \frac{\partial g(y;\beta)}{\partial\beta}\Big[f\{p_a(y), g(y;\beta)\} + g(y;\beta)\,f_2'\{p_a(y), g(y;\beta)\}\Big]\,dy. \qquad\text{(eq. 8)}$$

**Examples (Corollary 1).** For the squared $L_2$ distance, $f(p,q) = (p-q)^2/q$, the bracket equals $2\{g(y;\beta) - p_a(y)\}$; for Kullback-Leibler, $f(p,q) = (p/q)\log(p/q)$, it equals $1 - p_a(y)/g(y;\beta)$ in the source's normalization. In particular, projecting in KL onto the exponential family $g(y;\beta) = \exp\{\beta^{\top}b(y) - C(\beta)\}$ (Example 1a) gives the moment-matching equation

$$\int b(y)\,g(y;\beta_0)\,dy = E\big[E\{b(Y) \mid X, A = a\}\big],$$

and projecting in $L_2$ onto the truncated series $g(y;\beta) = q(y) + \beta^{\top}b(y)$ (Example 1b) gives $\int b(y)\{q(y) + \beta_0^{\top}b(y) - p_a(y)\}\,dy = 0$.

## Expansion

Proposition 1 is the first-order condition $\partial_\beta D_f = 0$ computed by the chain rule, since $\beta$ enters $D_f$ both through $f(p_a, g)$ and through the weight $g$. The key point is that every such $m(\beta)$ is an integral functional of the counterfactual density, i.e. a mean $E[E\{h(Y) \mid X, A = a\}]$ of a transformation of $Y^a$, which is why its efficient influence function has the familiar augmented-IPW form described in [efficient influence functions for counterfactual density functionals](efficient-influence-function-counterfactual-density-functionals.md). For the exponential family, $\int \partial_\beta g = 0$ makes the constant $1$ in the KL bracket drop out.

## Sources

- E. H. Kennedy, S. Balakrishnan and L. Wasserman, *Semiparametric counterfactual density estimation*, Biometrika (2023). <https://doi.org/10.1093/biomet/asad017>
