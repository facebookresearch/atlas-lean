# Asymptotic stability of linear ODEs with eigenvalues in the open left half-plane

Let
$n \ge 0$ and let $A$ be a real $n \times n$ matrix such that every complex eigenvalue $\mu$ of $A$
(an eigenvalue of $A$ viewed as a complex matrix acting on $\mathbb{C}^n$) satisfies
$\operatorname{Re} \mu < 0$. Let $x : \mathbb{R} \to \mathbb{R}^n$ be a function that, at every
$t > 0$, is differentiable with derivative $x'(t) = A\,x(t)$. Then $\|x(t)\| \to 0$ as
$t \to \infty$, where $\|\cdot\|$ is the sup norm on $\mathbb{R}^n$.

## Sources

- Classical linear stability theory; Hirsch-Smale-Devaney. Problem `linear_ode_asymptotic_stability` of the lean-eval benchmark.
