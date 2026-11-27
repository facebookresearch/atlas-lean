# Optimal threshold for maximal long-run harvesting yield

**Setting.** An unharvested population density follows

$$dX_t = X_t\mu(X_t)\,dt + \sigma(X_t)\,dB_t,$$

with continuous $\mu, \sigma$ on $(0,\infty)$, $\sigma > 0$ and the Engelbert–Schmidt local integrability condition, so that weak solutions exist and are unique; both boundaries $0$ and $\infty$ are natural (no extinction, no explosion). Let $S'(x) = \exp\big(-\int_c^x 2\mu(y)y/\sigma^2(y)\,dy\big)$ be the scale density and $m'(x) = 2/(\sigma^2(x)S'(x))$ the speed density. A harvesting strategy is a non-decreasing, right-continuous adapted process $Z$ with $Z_{0-} = 0$ (the cumulative harvest), giving

$$dX^Z_t = X^Z_t\mu(X^Z_t)\,dt + \sigma(X^Z_t)\,dB_t - dZ_t .$$

Assume (A1) $\mu$ is non-increasing with $\mu(0+) > \eta$ and $\mu(\infty) < -\eta$ for some $\eta > 0$; (A2) $x\mu(x)$ has a unique maximizer $\hat x$, increasing before and decreasing after it; (A3) $m((x,y))$ stays finite as $x \downarrow 0$.

**Theorem (expected average yield).** The optimal strategy is the local-time push at a threshold $b^*$: harvest $(x - b^*)^+$ immediately and then $Z_t = L(t, b^*)$, the local time that reflects $X^Z$ downward at $b^*$. The threshold $b^*$ is the unique zero of $f(x) = \int_0^x\big(\mu(y)y - \mu(x)x\big)m'(y)\,dy$, and the maximal long-run expected average yield is

$$\ell^* = \limsup_{T\to\infty}\frac1T\mathbb{E}_x[Z^{b^*}_T] = \mu(b^*)b^* = \frac{1}{S'(b^*)\,m((0,b^*))} = \sup_{b > 0}\frac{1}{S'(b)\,m((0,b))},$$

and $\liminf_{T\to\infty}\frac1T\mathbb{E}_x\int_0^T dZ_s \le \ell^*$ for every admissible $Z$. Moreover $b^* < \hat x$: harvesting starts below the deterministic maximum-sustainable-yield level.

**Theorem (pathwise yield).** For every reflection policy at level $b$, almost surely $Z^b_T/T \to 1/(S'(b)m((0,b)))$. Under pathwise uniqueness and a Yamada–Watanabe modulus for $\sigma$, existence of an invariant probability measure, and integrability of $\sigma v'$ for the value function $v$, every admissible strategy satisfies $\liminf_{T\to\infty} Z_T/T \le \ell^* = \lim_{T\to\infty} Z^{b^*}_T/T$ almost surely.

**Theorem (Abelian limit).** If $V_r$ is the maximal expected discounted yield at rate $r$, with optimal boundary $x^*_r$, then $x^*_r$ increases to $b^*$ as $r \downarrow 0$ and $\lim_{r\to0+} rV_r(x) = \mu(b^*)b^* = \ell^*$ for all $x$.

## Expansion

A verification lemma shows that any $C^2$ function $v$ with $v' \ge 1$ and $\mathcal{A}v \le \ell$ bounds the expected average yield by $\ell$, via Itô's formula applied to $v(X^Z)$: each unit harvested lowers $v$ by at least one unit while the drift raises it by at most $\ell$. Solving the free-boundary problem $\frac{d}{dx}(u'/S') = \ell m'$ on $(0,b)$ with $u'(0+)/S'(0+) = 0$ and smooth fit $u'(b) = 1$, $u''(b) = 0$ yields $\ell = 1/(S'(b)m((0,b))) = \mu(b)b$, and maximizing over $b$ gives the zero of $f$. For the reflected process, the ratio ergodic theorem gives $Z^b_T/T \to \int \mu(y)y\,m(dy)/m((0,b))$, which an integration by parts identifies with $1/(S'(b)m((0,b)))$; a comparison theorem keeps harvested paths below unharvested ones.

## Sources

- Luis H.R. Alvarez E., Alexandru Hening, "Optimal sustainable harvesting of populations in random environments", Stochastic Processes and their Applications 150 (2022), 678–698, <https://doi.org/10.1016/j.spa.2019.02.008>. Published version of arXiv:1807.02464, cited next; locators there refer to the arXiv version.
- Luis H. R. Alvarez E., Alexandru Hening, "Optimal sustainable harvesting of populations in random environments", arXiv (2018). Section 2 (model, Assumptions, Lemmas 2.1–2.3, Proposition 2.1, main theorems on expected and almost-sure optimality), Section 3 (Lemma 3.1, Theorem 3.1). <https://doi.org/10.48550/arXiv.1807.02464>
