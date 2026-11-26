# Global bifurcation branches and spike-like steady states in signal-dependent chemotaxis

**Model.** On $(0,L)$ with Neumann conditions, consider

$$u_t = u_{xx} - \chi_0\Big(\frac{u^m}{(1+v)^\beta}v_x\Big)_x + au - bu^{1+\alpha}, \qquad 0 = v_{xx} - \mu v + \nu u^\gamma,$$

with $\alpha, \gamma, m, \mu, \nu > 0$, $a, b, \beta \ge 0$ and $\chi_0 \in \mathbb{R}$. Either $a, b > 0$ (non-minimal model, $u^* = (a/b)^{1/\alpha}$) or $a = b = 0$ (minimal model, any $u^* > 0$, with perturbations of zero mean); in both cases $v^* = \nu (u^*)^\gamma/\mu$. With Neumann eigenvalues $\lambda_n = n^2\pi^2/L^2$ and eigenfunctions $\phi_n = \cos(n\pi x/L)$, the linearization at $(u^*,v^*)$ has eigenvalues

$$\sigma_n(\chi_0) = -\lambda_n + \chi_0\,\nu\gamma\,\frac{(u^*)^{m+\gamma-1}}{(1+v^*)^\beta}\,\frac{\lambda_n}{\mu+\lambda_n} - a\alpha,$$

and the constant state is linearly stable for $\chi_0 < \chi^*$ and unstable for $\chi_0 > \chi^*$, where

$$\chi^*(u^*) = \inf_{n\ge1}\chi_n(u^*), \qquad \chi_n(u^*) = \frac{(1+v^*)^\beta}{\nu\gamma(u^*)^{m+\gamma-1}}\,\frac{(\lambda_n + a\alpha)(\mu + \lambda_n)}{\lambda_n}.$$

A mode $n_0 \ge 1$ with $\chi_{n_0} = \chi^*$ is a bifurcation mode; it is unique when $L \in (L_{k-1}, L_k)$ with $L_0 = 0$, $L_k = \pi\sqrt{k(k+1)}/(a\alpha\mu)^{1/4}$ (then $n_0 = k$), and for the minimal model $n_0 = 1$ for every $L$.

**Theorem (global branches).** Let $n_0$ be the unique bifurcation mode with $\beta_{n_0} \ne 0$, and let $\mathcal{C}^\pm_{n_0}$ be the maximal connected continua of positive stationary solutions in $(0,\infty)\times H^2$ that emanate from $(\chi^*, u^*)$ along the local half-branches $\Gamma^\pm_{n_0}$ (each excluding the opposite half-branch).
1. Each $\mathcal{C}^\pm_{n_0}$ is either non-compact, or meets the constant state $u^*$ at another parameter $\hat\chi_0 \ne \chi^*$, or contains a point $(\hat\chi_0, u^* + w)$ with $w \ne 0$ in the complement of the bifurcation direction (a global continuation alternative; here the complement is taken to $\phi_{n_0}$ in $L^2$).
2. If $a, b > 0$, $0 < \gamma \le 1 + \alpha$ and $1 \le m \le \alpha + 2$, a non-compact branch extends to $\sup\{\chi_0\} = +\infty$.
3. For the minimal model with $1 \le m \le 2$ and $0 < \gamma \le 1$, both branches $\mathcal{C}^\pm_1$ are unbounded in $\chi_0$; nonconstant solutions on $\mathcal{C}^+_1$ are strictly decreasing and on $\mathcal{C}^-_1$ strictly increasing; and along $\chi_j \to \infty$ the densities concentrate at a boundary point: $\int_0^L f u_j \to Lu^* f(0)$ (respectively $Lu^* f(L)$) for every $f \in C([0,L])$, so $\max u_j \to \infty$.

**Theorem (spike-like steady states).** Let $(u_n, v_n)$ be positive nonconstant stationary solutions with $\chi_0 = \chi_n \to \infty$ (and $\int_0^L u_n = Lu^*$ in the minimal model). If $\liminf_n \max u_n > u^*$, then along a subsequence there is $x^* \in [0,L]$ with $\max_{[x^*-\delta, x^*+\delta]\cap[0,L]}|(u_{n_k})_x| \to \infty$ for every $\delta > 0$. In the non-minimal model with $0 < \gamma < 1 + \alpha$, moreover $u_{n_k}^\gamma \rightharpoonup c$ weakly in $L^{(1+\alpha)/\gamma}$ and $v_{n_k} \to \nu c/\mu$ in $C^1$ for a constant $0 \le c \le (u^*)^\gamma$: the spikes carry no Dirac mass and the signal flattens.

## Depends on

- [Pitchfork bifurcation of constant equilibria in signal-dependent chemotaxis](pitchfork-bifurcation-of-constant-equilibria-in-signal-dependent-chemotaxis.md)

## Expansion

The alternative in part 1 is a global continuation of the local half-branches. A priori bounds on positive nonconstant stationary solutions for bounded $\chi_0$, available under the stated exponent restrictions, rule out blow-up of the branch at finite $\chi_0$, so non-compactness forces $\chi_0 \to \infty$. In the minimal model with $n_0 = 1$, monotonicity of solutions is preserved along the branch, which excludes the other alternatives. Integrating the stationary equation gives $a\int u_n = b\int u_n^{1+\alpha}$, and every nonconstant steady state satisfies $\int u^{1+\alpha} < L(u^*)^{1+\alpha}$; this $L^{1+\alpha}$ bound, uniform in $\chi_0$, prevents concentration of mass in the non-minimal model, so steep gradients appear without a Dirac limit.

## Sources

- L. Chen, I. Ruau and W. Shen, "Chemotaxis models with signal-dependent sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions", arXiv:2610.20976 (2026), Theorems 1.3 and 1.4 and Remark 1.3, proved in Sections 4 and 5 (numerical evidence in Section 6), <https://doi.org/10.48550/arXiv.2610.20976>.
