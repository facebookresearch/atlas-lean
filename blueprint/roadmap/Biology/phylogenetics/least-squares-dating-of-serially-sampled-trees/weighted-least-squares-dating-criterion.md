# Weighted least-squares dating criterion

Let $T$ be a rooted binary tree with $n \ge 2$ tips, nodes numbered $1, \dots, 2n-1$ with root $1$, internal nodes $1, \dots, n-1$ and tips $n, \dots, 2n-1$, and let $a(i)$ denote the parent of node $i \ge 2$. Each branch $(a(i), i)$ carries an estimated length $b_i \ge 0$ in substitutions per site from an alignment of $s$ sites; the tip dates $t_n, \dots, t_{2n-1}$ are known; the internal dates $t_1, \dots, t_{n-1}$ and the substitution rate $\omega > 0$ are unknown. Assume the Gaussian clock model

$$b_i \;=\; \omega\,(t_i - t_{a(i)}) + \varepsilon_i, \qquad \varepsilon_i \sim \mathcal N(0, \sigma_i^2) \ \text{independent},$$

with Poisson-motivated variances $\sigma_i^2 = \omega(t_i - t_{a(i)})/s$, estimated by the smoothed plug-in $\hat\sigma_i^2 = (b_i + c/s)/s$ for a constant $c > 0$. The estimates minimize the weighted least-squares criterion

$$\varphi(\omega, t_1, \dots, t_{n-1}) \;=\; \sum_{i=2}^{2n-1} w_i\,\bigl(b_i - \omega\,(t_i - t_{a(i)})\bigr)^2, \qquad w_i = 1/\hat\sigma_i^2 > 0 .$$

1. If the tip dates are not all equal, then in the variables $\beta_i = \omega t_i$ ($i \le n-1$) the criterion becomes a strictly convex quadratic function of $(\omega, \beta_1, \dots, \beta_{n-1})$, so $\varphi$ has a unique minimizer over $\omega > 0$ whenever that minimizer has $\omega > 0$; if all tips are contemporaneous, $\omega$ is not identifiable.
2. The criterion tolerates uncorrelated violations of the clock: if the rate on branch $i$ is $\omega_i \sim \mathcal N(\omega, \xi^2)$, independent of the sampling noise, then $b_i \sim \mathcal N\bigl(\omega\Delta_i,\ \xi^2\Delta_i^2 + \omega\Delta_i/s\bigr)$ with $\Delta_i = t_i - t_{a(i)}$, again a Gaussian model whose variance increases with branch length.

## Expansion

With $\beta_i = \omega t_i$, the residual of an internal branch is $b_i - \beta_i + \beta_{a(i)}$ and that of a tip branch is $b_i - \omega t_i + \beta_{a(i)}$, both affine in $(\omega, \beta)$, so $\varphi$ is a positive-weighted sum of squares of affine functions. It is strictly convex if and only if the linear part is injective. A kernel vector satisfies $\beta_i = \beta_{a(i)}$ along every internal branch, so all $\beta_i$ equal a common value $B$, and $\omega t_i = B$ at every tip; two distinct tip dates force $\omega = 0$ and then $B = 0$. Strict convexity transfers to $\varphi$ because $(\omega, t) \mapsto (\omega, \omega t)$ is a bijection on $\omega > 0$. The relaxed-clock claim is the sum of independent Gaussians $(\omega_i - \omega)\Delta_i$ and $\varepsilon_i$. The smoothing constant $c$ prevents infinite weights on zero-length branches: $c = 1$ is Laplace's rule of succession, and $c = 10$ performed best in simulations. Adding the temporal precedence constraints $t_i \ge t_{a(i)}$ gives a convex quadratic program, solved by an active-set method in which each iteration is again a tree-structured least-squares problem.

## Sources

- T.-H. To, M. Jung, S. Lycett, O. Gascuel, "Fast dating using least-squares criteria and algorithms", *Systematic Biology* 65(1) (2016) 82–97, sections "Preliminaries and Notation" and "Outline of the Approach" (Equations (1)–(4) and (2b), and the relaxed-clock remark following Equation (4)), <https://doi.org/10.1093/sysbio/syv068> (PMC4678253).
