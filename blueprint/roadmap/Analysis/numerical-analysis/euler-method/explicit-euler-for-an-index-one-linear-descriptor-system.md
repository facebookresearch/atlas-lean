# Explicit Euler for an index-one linear descriptor system

Let $A \in \mathbb R^{n \times n}$, $B \in \mathbb R^{n \times m}$, $C \in \mathbb R^{m \times n}$ and an invertible
$D \in \mathbb R^{m \times m}$, and let $f : \mathbb R \to \mathbb R^n$ and $g : \mathbb R \to \mathbb R^m$ be twice continuously
differentiable. Consider the index-one descriptor system

$$x' = A x + B y + f(t), \qquad 0 = C x + D y + g(t),$$

as produced by modified nodal analysis of a linear circuit, on $[t_0, T]$ with $x(t_0) = x_0$ and the consistent value
$y(t_0) = -D^{-1}(C x_0 + g(t_0))$. Eliminating $y = -D^{-1}(C x + g)$ gives the reduced equation
$x' = (A - B D^{-1} C) x + f(t) - B D^{-1} g(t)$. Fix norms on $\mathbb R^n$ and $\mathbb R^m$ with the induced operator norms, and put $\hat A = A - B D^{-1} C$. Let $X_n$ be the explicit Euler sequence of the reduced equation with step $h$ from an arbitrary $X_0 \in \mathbb R^n$, and
reconstruct $Y_n = -D^{-1}(C X_n + g(t_0 + n h))$. Then there is a constant $K$, independent of $h$ and $X_0$, such that for every $h \in (0, T - t_0]$ and every
$n$ with $n h \le T - t_0$,

$$|X_n - x(t_0 + n h)| \le e^{\|\hat A\|(T - t_0)}\,|X_0 - x_0| + K h, \qquad |Y_n - y(t_0 + n h)| \le \|D^{-1} C\|\,\bigl(e^{\|\hat A\|(T - t_0)}\,|X_0 - x_0| + K h\bigr) .$$

For $X_0 = x_0$ the first bound is the [first-order convergence of the explicit Euler method](explicit-euler-first-order-convergence.md)
for the reduced right-hand side, which is twice continuously differentiable and globally Lipschitz in $x$; the initial-error term follows because the Euler sequences from $X_0$ and from $x_0$ differ by $(I + h\hat A)^n (X_0 - x_0)$; the second bound follows
because $Y_n - y(t_0 + nh) = -D^{-1} C\,(X_n - x(t_0 + nh))$.

## Depends on

- [First-order convergence of the explicit Euler method](explicit-euler-first-order-convergence.md)

## Sources

- E. Hairer and G. Wanner, *Solving Ordinary Differential Equations II: Stiff and Differential-Algebraic Problems*, 2nd edition, Springer, 1996, Chapter VI (index-one problems and the state-space form).
- C.-W. Ho, A. E. Ruehli and P. A. Brennan, "The modified nodal approach to network analysis", *IEEE Transactions on Circuits and Systems* 22(6):504–509, 1975.
