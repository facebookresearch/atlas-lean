# Picard iterates converge

Let $E$ be a real Banach space, let
$f : \mathbb{R} \times E \to E$ be continuous, and let $L \ge 0$ be such that $f(t, \cdot)$ is
$L$-Lipschitz for every $t \in \mathbb{R}$. Fix $t_0 \in \mathbb{R}$ and $x_0 \in E$, and let
$(u_n)_{n \ge 0}$ be maps $\mathbb{R} \to E$ with $u_0(t) = x_0$ and
$u_{n+1}(t) = x_0 + \int_{t_0}^{t} f(s, u_n(s))\,ds$ for all $n$ and $t$. Then there is a map
$x : \mathbb{R} \to E$ with $x(t_0) = x_0$ and $x'(t) = f(t, x(t))$ for every $t \in \mathbb{R}$,
such that $u_n(t) \to x(t)$ as $n \to \infty$ for every $t \in \mathbb{R}$.

Proof: Sum the factorially bounded successive differences, obtaining locally uniform convergence
on every compact time interval. Pass the recursion through the integral and apply the fundamental
theorem of calculus. This is the argument of Teschl, Theorem 2.5 and Corollary 2.6 (Section 2.3),
for the Picard iterates (2.13) of Section 2.2, with a constant global Lipschitz constant.

## Sources

- `Mathlib/docs/undergrad.yaml`, section `Numerical Analysis` / `Iterative methods of solving systems of real and vector-valued equations`, entry `Picard method` (unmapped); G. Teschl, Ordinary Differential Equations and Dynamical Systems, Section 2.3; stable ref https://en.wikipedia.org/wiki/Picard%E2%80%93Lindel%C3%B6f_theorem.
