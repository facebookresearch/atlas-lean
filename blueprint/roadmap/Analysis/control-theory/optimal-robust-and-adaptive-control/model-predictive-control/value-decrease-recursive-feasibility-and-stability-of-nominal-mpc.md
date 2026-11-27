# Value decrease, recursive feasibility and stability of nominal model predictive control

Let $f : \mathbb{R}^n \times \mathbb{R}^m \to \mathbb{R}^n$ with $f(0, 0) = 0$, let $\mathbb{X} \subseteq \mathbb{R}^n$ and $\mathbb{U} \subseteq \mathbb{R}^m$ be constraint sets and $\mathbb{X}_f \subseteq \mathbb{X}$ a terminal set, all containing the origin, let $Q \in \mathbb{R}^{n \times n}$ and $R \in \mathbb{R}^{m \times m}$ be positive definite with stage cost $\ell(x, u) = x^\top Q x + u^\top R u$, and let $V_f : \mathbb{X}_f \to [0, \infty)$ with $V_f(0) = 0$. Fix a horizon $N \ge 1$. For an initial state $x$ and inputs $\mathbf{u} = (u_0, \dots, u_{N-1})$, let $x_0 = x$, $x_{i+1} = f(x_i, u_i)$, call $\mathbf{u}$ **feasible** if $u_i \in \mathbb{U}$ and $x_i \in \mathbb{X}$ for $i < N$ and $x_N \in \mathbb{X}_f$, let $J_N(x, \mathbf{u}) = \sum_{i < N} \ell(x_i, u_i) + V_f(x_N)$, and let $\mathbb{X}_N$ be the set of $x$ that admit a feasible $\mathbf{u}$. Assume:

- (terminal ingredients) there is $\kappa : \mathbb{X}_f \to \mathbb{U}$ with $\kappa(0) = 0$ such that for every $x \in \mathbb{X}_f$, $f(x, \kappa(x)) \in \mathbb{X}_f$ and $V_f(f(x, \kappa(x))) - V_f(x) \le -\ell(x, \kappa(x))$;
- (local bound) some ball $\{\|x\| < r\}$, $r > 0$, lies in $\mathbb{X}_f$, and $V_f(x) \le \beta \|x\|^2$ there, with $\beta \ge 0$;
- (exact optimization) for every $x \in \mathbb{X}_N$ the infimum $V_N(x)$ of $J_N(x, \cdot)$ over feasible inputs is attained, and $\kappa_N(x)$ denotes the first input $u_0$ of some chosen minimizer.

Let $\alpha > 0$ be the smallest eigenvalue of $Q$. Then:

1. **Value decrease.** For every $x \in \mathbb{X}_N$, $f(x, \kappa_N(x)) \in \mathbb{X}_N$ and $V_N(f(x, \kappa_N(x))) \le V_N(x) - \ell(x, \kappa_N(x))$.
2. **Quadratic bounds.** $\alpha \|x\|^2 \le V_N(x)$ for every $x \in \mathbb{X}_N$, and $V_N(x) \le V_f(x) \le \beta \|x\|^2$ whenever $\|x\| < r$.
3. **Recursive feasibility and convergence.** For every $x_0 \in \mathbb{X}_N$, the closed loop $x_{k+1} = f(x_k, \kappa_N(x_k))$ stays in $\mathbb{X}_N$ and $x_k \to 0$.
4. **Stability.** For every $\varepsilon > 0$ there is $\delta > 0$ such that every $x_0 \in \mathbb{X}_N$ with $\|x_0\| < \delta$ gives $\|x_k\| < \varepsilon$ for all $k \ge 0$; one may take $\delta = \min(r, \varepsilon \sqrt{\alpha / \beta})$, or $\delta = r$ if $\beta = 0$.

No continuity of $f$, of $V_N$ or of the selection $\kappa_N$ is used, and nothing is claimed for approximate optimizers.

**Proof.** For part 1, let $\mathbf{u}^\star$ be the chosen minimizer at $x$, with states $x_0^\star = x, \dots, x_N^\star \in \mathbb{X}_f$. The shifted sequence $\tilde{\mathbf{u}} = (u_1^\star, \dots, u_{N-1}^\star, \kappa(x_N^\star))$ is feasible from $x^+ = f(x, u_0^\star)$: its states are $x_1^\star, \dots, x_N^\star$ and then $f(x_N^\star, \kappa(x_N^\star)) \in \mathbb{X}_f$, with $\mathbb{X}_f \subseteq \mathbb{X}$. Its cost is

$$J_N(x^+, \tilde{\mathbf{u}}) = V_N(x) - \ell(x, u_0^\star) + \ell(x_N^\star, \kappa(x_N^\star)) + V_f(f(x_N^\star, \kappa(x_N^\star))) - V_f(x_N^\star) \le V_N(x) - \ell(x, u_0^\star),$$

by the terminal decrease. For part 2, all terms of $J_N$ are nonnegative, so $V_N(x) \ge \ell(x, u_0) \ge x^\top Q x \ge \alpha\|x\|^2$. If $\|x\| < r$, applying $\kappa$ repeatedly from $x$ keeps the state in $\mathbb{X}_f$ and is feasible, and summing the terminal decrease over $N$ steps gives $J_N \le V_f(x)$. For part 3, part 1 gives invariance of $\mathbb{X}_N$; the sequence $V_N(x_k)$ is nonincreasing and nonnegative, hence convergent, and $\alpha\|x_k\|^2 \le \ell(x_k, \kappa_N(x_k)) \le V_N(x_k) - V_N(x_{k+1}) \to 0$. For part 4, if $\|x_0\| < \delta \le r$ then $\alpha\|x_k\|^2 \le V_N(x_k) \le V_N(x_0) \le \beta\|x_0\|^2 < \alpha\varepsilon^2$.

## Sources

- J. B. Rawlings, D. Q. Mayne and M. M. Diehl, *Model Predictive Control: Theory, Computation, and Design*, 2nd ed., Nob Hill Publishing, 2017, <https://sites.engineering.ucsb.edu/~jbraw/mpc/MPC-book-2nd-edition-1st-printing.pdf>, Section 2.4: Assumption 2.14 (basic stability assumption: terminal admissibility and decrease, and bounds on $\ell$ and $V_f$, p. 114), the descent property of the optimal value function (pp. 115–118) and Theorem 2.19 (upper and lower bounds, descent and asymptotic stability of the origin, pp. 119–120). The quadratic specialization, the explicit $\delta$ and the statement without continuity of the selection are derived on the page.
