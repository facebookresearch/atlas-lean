# Explicit Euler for an index-one linear descriptor system

Let $n$ and $m$ be finite index sets, let $A \in \mathbb R^{n \times n}$, $B \in \mathbb R^{n \times m}$,
$C \in \mathbb R^{m \times n}$ and an invertible $D \in \mathbb R^{m \times m}$, and let $f : \mathbb R \to \mathbb R^n$
and $g : \mathbb R \to \mathbb R^m$ be twice continuously differentiable. Let $t_0 < T$, and let $(x_0, y_0)$ be an
initial pair consistent at $t_0$: $C x_0 + D y_0 + g(t_0) = 0$. Consider the index-one descriptor system

$$x' = A x + B y + f(t), \qquad 0 = C x + D y + g(t),$$

as produced by modified nodal analysis of a linear circuit. A pair $(x, y)$ solves it on $[t_0, T]$ when at every
$t \in [t_0, T]$ the function $x$ has derivative $A x(t) + B y(t) + f(t)$ and $C x(t) + D y(t) + g(t) = 0$; no
regularity is asked of $y$.

The norms are the sup norms of $\mathbb R^n$ and $\mathbb R^m$ in these coordinates: $|v| = \max_i |v_i|$, the largest
absolute coordinate, when the index set is nonempty, and $|v| = 0$ when it is empty; $\|\cdot\|$ is the operator norm
they induce. Put $\hat A = A - B D^{-1} C$ and $L = \|\hat A\|$. Eliminating
$y = -D^{-1}(C x + g)$ gives the reduced equation $x' = \hat A x + f(t) - B D^{-1} g(t)$. For a step $h > 0$, an
explicit Euler sequence of the reduced equation is a sequence $(X_k)$, from an arbitrary $X_0 \in \mathbb R^n$, with
$X_{k+1} = X_k + h\,\bigl(\hat A X_k + f(t_0 + k h) - B D^{-1} g(t_0 + k h)\bigr)$; the algebraic values are
reconstructed at the same time samples, $Y_k = -D^{-1}(C X_k + g(t_0 + k h))$.

Then the system has a solution $(x, y)$ on $[t_0, T]$ with $x(t_0) = x_0$ and $y(t_0) = y_0$, and there is a constant
$K \ge 0$ such that for every solution $(x, y)$ on $[t_0, T]$ with $x(t_0) = x_0$, every step $h \in (0, T - t_0]$,
every explicit Euler sequence $(X_k)$ of the reduced equation with step $h$ and every $k$ with $k h \le T - t_0$,

$$|X_k - x(t_0 + k h)| \le e^{L (T - t_0)}\,|X_0 - x_0| + K h, \qquad |Y_k - y(t_0 + k h)| \le \|D^{-1} C\|\,\bigl(e^{L (T - t_0)}\,|X_0 - x_0| + K h\bigr).$$

The constant $K$ depends on neither $h$, nor $X_0$, nor the solution. The statement is about the sup norms of the
given coordinates and says nothing about other norms; a positive diagonal rescaling of the coordinates is another
instance of it, with its own $L$, $\|D^{-1} C\|$ and $K$.

For $X_0 = x_0$, the state bound is the
[first-order convergence of the explicit Euler method](explicit-euler-first-order-convergence.md) for the reduced
right-hand side, which is twice continuously differentiable and Lipschitz in the state with constant $L$. Two
explicit Euler sequences with the same step separate after $k$ steps by at most $e^{L k h}$ times their initial
difference, which gives the initial-error term, and the algebraic bound follows because
$Y_k - y(t_0 + k h) = -D^{-1} C\,\bigl(X_k - x(t_0 + k h)\bigr)$.

## Sources

- E. Hairer and G. Wanner, *Solving Ordinary Differential Equations II: Stiff and Differential-Algebraic Problems*, 2nd edition, Springer, 1996, Chapter VI (index-one problems and the state-space form).
- C.-W. Ho, A. E. Ruehli and P. A. Brennan, "The modified nodal approach to network analysis", *IEEE Transactions on Circuits and Systems* 22(6):504–509, 1975.
