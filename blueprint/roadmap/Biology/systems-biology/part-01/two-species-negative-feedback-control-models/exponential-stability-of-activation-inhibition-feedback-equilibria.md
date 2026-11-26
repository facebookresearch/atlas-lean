# Exponential stability of activation–inhibition feedback equilibria

**Model.** For concentrations $x, y \ge 0$ consider

$$\dot y = -\alpha y + u_y + f(x,y), \qquad \dot x = -\beta x + u_x + g(x,y),$$

with clearance rates $\alpha, \beta > 0$, constant production rates $u_x, u_y \ge 0$, activation function $f$ (of $y$ by $x$) and inhibition function $g$ (of $x$ by $y$), under the assumptions:

1. $f, g : \mathbb{R}_+ \times \mathbb{R}_+ \to \mathbb{R}$ are piecewise continuously differentiable (so solutions exist and are unique);
2. for each fixed $y$, $f(\cdot,y)$ is non-decreasing and $g(\cdot,y)$ is non-increasing;
3. for each fixed $x$, $f(x,\cdot)$ is non-decreasing and $g(x,\cdot)$ is non-increasing.

An equilibrium $z_E$ of $\dot z = h(z,u)$ under a constant input $u_E$ is **exponentially stable with rate at least $\rho$** if trajectories starting near $z_E$, under constant inputs near $u_E$, approach it at least as fast as a constant multiple of $e^{-\rho t}$ (Definition 1 of the source gives the explicit bounds).

**Theorem 1.** (i) Equilibria are the solutions of $\alpha y = u_y + f(x,y)$, $\beta x = u_x + g(x,y)$. (ii) Let $(x_0,y_0)$ be an equilibrium at which $f,g$ are differentiable, with partial derivatives $f_x, f_y, g_x, g_y$ evaluated there. If

$$\alpha + \beta - g_x - f_y > 0 \quad\text{and}\quad (\alpha - f_y)(\beta - g_x) - f_x\, g_y > 0,$$

then $(x_0, y_0)$ is exponentially stable. (iii) With

$$A = \begin{pmatrix} -\alpha + f_y & f_x \\ g_y & -\beta + g_x \end{pmatrix},$$

if there are $\rho > 0$ and $P \succ 0$ with $A^{\mathsf T} P + P A + 2\rho P \prec 0$, the rate of convergence is at least $\rho$.

**Corollary 1 ($f$ independent of $y$).** If $f = f(x)$, every equilibrium at which $f, g$ are differentiable is exponentially stable, with no further condition.

**Corollary 2 ($f = f(x)$ and $g = g(y)$).** Equilibria solve $\alpha y = u_y + f(x)$, $\beta x = u_x + g(y)$; if $g$ is invertible they are the intersections of the graphs $y = (u_y + f(x))/\alpha$ and $y = g^{-1}(\beta x - u_x)$, unique iff these graphs meet once, and each is exponentially stable.

## Proof depends on

- [Routh–Hurwitz: a real 2 × 2 matrix is Hurwitz iff tr M < 0 < det M](../../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/is-hurwitz-iff-trace-neg-and-det-pos.md)

## Expansion

Shifting coordinates to the equilibrium and linearizing gives $\dot\delta = A\delta$ with characteristic polynomial

$$p(s) = s^2 + (\alpha + \beta - g_x - f_y)\,s + (\alpha - f_y)(\beta - g_x) - f_x g_y .$$

A real quadratic is Hurwitz iff both coefficients are positive, which is condition (ii); exponential stability of the linearization implies local exponential stability of the nonlinear system (Lyapunov's indirect method), and the LMI in (iii) is a Lyapunov certificate with decay rate $\rho$. In Corollary 1, $f_y = 0$; since $g_x \le 0$, $g_y \le 0$ and $f_x \ge 0$, the trace coefficient is at least $\alpha + \beta > 0$ and the constant coefficient is at least $\alpha\beta > 0$. The sign structure $f_x g_y \le 0$ is the negative feedback: activation of $y$ by $x$ composed with inhibition of $x$ by $y$.

Instances include a biomolecular repressor circuit, a glucose–insulin loop with Hill-type insulin secretion, and a stretch-reflex model where the firing rates obey Hill-type input–output curves at steady state; in each the equilibrium is the unique graph intersection and Corollary 1 or 2 certifies its stability.

## Sources

- A. M. Ponsiglione, F. Montefusco, L. Donisi, A. Tedesco, C. Cosentino, A. Merola, M. Romano, F. Amato, "A General Approach for the Modelling of Negative Feedback Physiological Control Systems", Bioengineering 10 (2023) 835, Equation (1), Assumption 1, Definition 1, Theorem 1 and Corollaries 1–2, <https://doi.org/10.3390/bioengineering10070835>, PMCID PMC10376068.
