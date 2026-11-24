# The increment of an explicit Runge–Kutta method is Lipschitz

Let $f : [x_0, X] \times \mathbb{R}^d \to \mathbb{R}^d$ be continuous and Lipschitz in its second argument with constant $L$, uniformly in the first. Consider an explicit $R$-stage Runge–Kutta method with coefficients $c_r$, $a_r$ and $b_{rs}$ ($s < r$), so that $y_{n+1} = y_n + h\Phi(x_n, y_n; h)$ with

$$\Phi(x, y; h) = \sum_{r=1}^R c_r k_r, \qquad k_1 = f(x, y), \qquad k_r = f\Big(x + a_r h,\ y + h\sum_{s<r} b_{rs}k_s\Big),$$

where the stage abscissae $x + a_r h$ are assumed to stay in $[x_0, X]$. Let $\beta = \max_r \sum_{s<r}|b_{rs}|$ and $\gamma = \sum_r |c_r|$.

1. **Stage bound.** For $h \ge 0$ and $y, z \in \mathbb{R}^d$, the stages satisfy $\|k_r(y) - k_r(z)\| \le L(1 + hL\beta)^{r-1}\|y - z\|$.
2. **Increment bound.** Hence $\|\Phi(x, y; h) - \Phi(x, z; h)\| \le L_\Phi\|y - z\|$ for $0 \le h \le h_0$, with $L_\Phi = L\gamma(1 + h_0L\beta)^{R-1}$.
3. **Convergence.** If moreover $\sum_r c_r = 1$, the method is consistent, $\Phi(x, y; 0) = f(x, y)$, and, for starting values $y_0(h) \to y(x_0)$, its global error tends to $0$ with $h$; if it has order of accuracy $p$, so that the truncation error $T_n = \frac{y(x_{n+1}) - y(x_n)}{h} - \Phi(x_n, y(x_n); h)$ along the exact solution is at most $Kh^p$, then, starting from the exact initial value, the global error is at most $\frac{K}{L_\Phi}\big(e^{L_\Phi(X - x_0)} - 1\big)h^p$, read as $K(X - x_0)h^p$ when $L_\Phi = 0$.

**Proof.** Part 1 is induction on $r$. For $r = 1$ it is the Lipschitz condition. If it holds for all $s < r$, then

$$\|k_r(y) - k_r(z)\| \le L\Big(\|y - z\| + h\sum_{s<r}|b_{rs}|\,\|k_s(y) - k_s(z)\|\Big) \le L\|y - z\|\big(1 + hL\beta(1 + hL\beta)^{r-2}\big),$$

and $1 + t(1 + t)^{r-2} \le (1 + t)^{r-1}$ for $t \ge 0$. Part 2 follows by summing with weights $|c_r|$ and bounding $(1 + hL\beta)^{r-1}$ by $(1 + h_0L\beta)^{R-1}$. In part 3, at $h = 0$ every stage equals $f(x, y)$, so $\Phi(x, y; 0) = (\sum_r c_r) f(x, y)$; consistency, continuity of $\Phi$ and the Lipschitz bound give convergence. For the order-$p$ bound, the recursion of the linked page with the truncation error in place of its defect gives $\|e_{n+1}\| \le (1 + hL_\Phi)\|e_n\| + Kh^{p+1}$, so from $e_0 = 0$ the geometric sum gives $\|e_n\| \le Kh^p\big((1 + hL_\Phi)^n - 1\big)/L_\Phi \le \frac{K}{L_\Phi}\big(e^{L_\Phi(X - x_0)} - 1\big)h^p$ for $x_n \le X$.

## Proof depends on

- [Global error of a one-step method from its local defect](../euler-method/global-error-of-a-one-step-method-from-its-local-defect.md): the global error bound from a Lipschitz increment and the local truncation error

## Background

- [Explicit Runge–Kutta method](explicit-rk.md): the Butcher tableau and the stages
- [Consistency of explicit Runge–Kutta methods](rk-step-sub-inv-smul-tendsto.md): the increment tends to the vector field as the step shrinks

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, University of Oxford, 2014, <https://people.maths.ox.ac.uk/suli/nsodes.pdf>, Chapter 2: Theorem 4 (global error of a one-step method whose increment satisfies the Lipschitz condition (24), p. 10), Definition 2 and the consistency condition (26) (p. 11), Theorem 5 (convergence under consistency and the Lipschitz condition (27), p. 12), Definition 3 (order of accuracy) and the explicit $R$-stage Runge–Kutta family (29) (p. 13). The explicit Lipschitz constant of the Runge–Kutta increment is derived on the page.
