# Existence and uniqueness for a consistent initial pair

Let $A \in \mathbb{R}^{n \times n}$, $B \in \mathbb{R}^{n \times m}$, $C \in \mathbb{R}^{m \times n}$ and $D \in \mathbb{R}^{m \times m}$ with $D$ invertible, on finite index sets, and let $f : \mathbb{R} \to \mathbb{R}^n$ and $g : \mathbb{R} \to \mathbb{R}^m$ be continuous. A solution of the descriptor system is a pair $(x, y)$ with $x$ differentiable and, for all $t$,

$$x'(t) = A x(t) + B y(t) + f(t), \qquad 0 = C x(t) + D y(t) + g(t).$$

Let $t_0 \in \mathbb{R}$ and let $(x_0, y_0)$ be consistent at $t_0$: $C x_0 + D y_0 + g(t_0) = 0$. Put $S = A - B D^{-1} C$. Then there is a solution $(x, y)$ with $x(t_0) = x_0$, $y(t_0) = y_0$ and $y$ continuous, such that for all $t$

$$x(t) = e^{(t - t_0) S} x_0 + \int_{t_0}^{t} e^{(t - s) S}\bigl(f(s) - B D^{-1} g(s)\bigr)\,ds, \qquad y(t) = -D^{-1}\bigl(C x(t) + g(t)\bigr),$$

and every solution $(x', y')$ with $x'(t_0) = x_0$ satisfies $x' = x$ and $y' = y$.
