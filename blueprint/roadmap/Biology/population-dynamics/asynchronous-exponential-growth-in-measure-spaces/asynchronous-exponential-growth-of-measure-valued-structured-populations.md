# Asynchronous exponential growth of measure-valued structured populations

**Model.** Let $\mathcal{M}^+(\mathbb{R}^+)$ be the finite nonnegative Radon measures on $\mathbb{R}^+ = [0,\infty)$, equipped with the flat norm

$$\|\mu\|_{BL^*} = \sup\Big\{ \int_{\mathbb{R}^+} \phi \, d\mu : \max\{\|\phi\|_\infty, |\phi|_{\mathrm{Lip}}\} \le 1 \Big\},$$

and let $E$ be the closure of the signed finite measures $\mathcal{M}(\mathbb{R}^+)$ in this norm. Consider the linear size-structured model

$$\partial_t \mu_t + \partial_x\big(b(x)\mu_t\big) + c(x)\mu_t = \int_{\mathbb{R}^+} \eta(x) \, d\mu_t(x), \qquad b(0) D_\lambda \mu_t(0) = 0, \qquad \mu_{t=0} = \mu_0,$$

where $b$ is the growth rate, $c$ the mortality rate, $\eta(x) \in \mathcal{M}^+(\mathbb{R}^+)$ the distribution of offspring sizes produced by an individual of size $x$, and $D_\lambda \mu_t(0)$ the Radon–Nikodym derivative with respect to Lebesgue measure at $0$. Write $\mathcal{B}\mu = -\partial_x(b\mu)$, $\mathcal{C}\mu = -c\mu$ and $\mathcal{N}\mu = \int \eta(x)\, d\mu(x)$.

**Hypotheses.** (i) $c \in BL(\mathbb{R}^+) \cap C^1(\mathbb{R}^+)$; (ii) $x \mapsto \eta(x)$ is bounded Lipschitz from $\mathbb{R}^+$ into $(\mathcal{M}^+(\mathbb{R}^+), \|\cdot\|_{BL^*})$; (iii) $b \in BL(\mathbb{R}^+) \cap C^1(\mathbb{R}^+)$ and $b > 0$; (iv) $b' \le 0$; (v) there is $\kappa > 0$ with $c(x) \ge |c'(x)| + \kappa$ for all $x \ge 0$.

**Theorem.** Under (i)–(iii) the model generates a strongly continuous positive semigroup $\mathcal{T}(t)$ on $E$ whose trajectories are the unique measure solutions. Under (i)–(v) exactly one of the following holds:

1. $\mathcal{T}(t)$ is uniformly exponentially stable (growth bound $\omega_0(\mathcal{T}) < 0$), so all solutions tend to zero;
2. there are $\lambda_* \ge 0$, an integer $k_* \ge 1$ and a finite-rank operator $P_*$ on $E$ such that $\mathcal{T}(t) = \mathcal{T}_*(t) + Q(t)$ with

$$\mathcal{T}_*(t) = e^{\lambda_* t} \sum_{j=0}^{k_*-1} \frac{t^j}{j!} \big(\mathcal{B} + \mathcal{C} + \mathcal{N} - \lambda_*\big)^j P_*, \qquad \|Q(t)\| \le M_\delta e^{(\lambda_* - \delta)t}$$

for some $\delta > 0$, $M_\delta \ge 1$ and all $t \ge 0$.

If in addition $\mathcal{T}(t)$ is irreducible (for every nonzero $\mu \in \mathcal{M}^+$ and nonzero nonnegative $\varphi \in BL$ some $t > 0$ gives $\int \varphi \, d(\mathcal{T}(t)\mu) > 0$), then in case 2 there is a rank-one operator $P_*$ with

$$\lim_{t \to \infty} e^{-\lambda_* t} \mathcal{T}(t) = P_*,$$

that is, the population exhibits asynchronous exponential growth: after normalization by $e^{\lambda_* t}$ every solution converges in the flat norm to a multiple of one fixed stable size distribution.

## Depends on

- [Irreducibility criterion for the measure-valued size-structured semigroup](irreducibility-criterion-for-the-measure-valued-size-structured-semigroup.md)

## Expansion

The proof shows that $\mathcal{T}(t)$ is quasi-compact on $E$: the transport–mortality part decays at rate at least $\kappa$ by (iv)–(v), while the birth operator $\mathcal{N}$ contributes a compact perturbation in the flat topology. For a quasi-compact semigroup the spectrum in $\{\mathrm{Re}\,\lambda \ge 0\}$ is a finite set of poles of finite algebraic multiplicity (Engel–Nagel, Ch. V, Thm 3.7), which gives the finite-rank decomposition. Positivity places the spectral bound $\lambda_*$ in the spectrum; irreducibility makes it a simple, strictly dominant pole, so the residue $P_*$ has rank one. Measures are needed because solutions may concentrate (e.g. discrete cohorts), which the classical $L^1$ theory cannot represent.

## Sources

- C. Düll, J. Z. Farkas, P. Gwiazda and A. Marciniak-Czochra, "Asynchronous exponential growth for structured population models in measure space", arXiv:2607.00658 (2026), Section 2 (model, Assumptions 2.4, Theorem 2.5), Proposition 3.1 and Theorem 3.7, Proposition 4.2 (quasi-compactness), <https://doi.org/10.48550/arXiv.2607.00658>.
