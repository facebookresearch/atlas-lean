# Global error of a one-step method from its local defect

Let $E$ be a normed space, $t_0 \in \mathbb{R}$, $D \ge 0$, and let $y : [t_0, t_0 + D] \to E$ be a function (the exact solution). Let $\Psi : [t_0, t_0 + D] \times E \times (0, h_0] \to E$ be an increment function that is Lipschitz in its second argument with constant $L \ge 0$: $\|\Psi(t, u; h) - \Psi(t, w; h)\| \le L\|u - w\|$. For a step $h \in (0, h_0]$ put $t_n = t_0 + nh$, define the one-step method $y_{n+1} = y_n + h\Psi(t_n, y_n; h)$ from a given starting value $y_0$, and the global error $e_n = y(t_n) - y_n$. Suppose the local defect satisfies

$$\|y(t_{n+1}) - y(t_n) - h\Psi(t_n, y(t_n); h)\| \le C h^2 \qquad \text{whenever } (n+1)h \le D,$$

with $C \ge 0$. Then for every $n$ with $nh \le D$,

$$\|e_n\| \le e^{LD}\|e_0\| + C D e^{LD} h .$$

In particular, with an exact start $y_0 = y(t_0)$ the method converges with order one, $\max_{nh \le D}\|e_n\| \le C D e^{LD} h$. Explicit Euler for $y' = f(t, y)$ is the case $\Psi(t, u; h) = f(t, u)$, whose local defect is $O(h^2)$ when $y$ is twice continuously differentiable.

**Proof.** Subtracting the method from the exact increment gives $e_{n+1} = e_n + h\big(\Psi(t_n, y(t_n); h) - \Psi(t_n, y_n; h)\big) + \delta_n$, with $\|\delta_n\| \le Ch^2$, so $\|e_{n+1}\| \le (1 + hL)\|e_n\| + Ch^2$. By induction, $\|e_n\| \le (1 + hL)^n \|e_0\| + Ch^2 \sum_{j < n} (1 + hL)^j \le e^{Lnh}\|e_0\| + n C h^2 e^{Lnh}$, using $1 + hL \le e^{hL}$; with $nh \le D$ this is the claim.

## Background

- [First-order convergence of the explicit Euler method](explicit-euler-first-order-convergence.md): the existing convergence statement for explicit Euler, which this bound makes quantitative for general one-step methods

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, University of Oxford, 2014, <https://people.maths.ox.ac.uk/suli/nsodes.pdf>, Section 2, the general one-step method (22), the truncation error (23) and Theorem 4 (pp. 9–10): for $\Phi$ Lipschitz in its second argument with constant $L_\Phi$, $|e_n| \le e^{L_\Phi(x_n - x_0)}|e_0| + \frac{e^{L_\Phi(x_n - x_0)} - 1}{L_\Phi}\, T$ with $T = \max_n |T_n|$, proved by the recursion $|e_{n+1}| \le (1 + hL_\Phi)|e_n| + h|T_n|$. The source works with scalar solutions in a region $R$; the normed-space form with an explicit $O(h^2)$ defect constant and the bound $(e^{LD} - 1)/L \le D e^{LD}$ is stated on the page.
