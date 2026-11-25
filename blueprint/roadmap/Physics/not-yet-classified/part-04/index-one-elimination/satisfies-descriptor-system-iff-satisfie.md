# Index-one reduction of a linear descriptor system

Let $n$ and $m$ be finite index sets, and let $A \in \mathbb{R}^{n\times n}$, $B \in \mathbb{R}^{n\times m}$, $C \in \mathbb{R}^{m\times n}$, $D \in \mathbb{R}^{m\times m}$. Assume $D$ is invertible. Let $f : \mathbb{R} \to \mathbb{R}^n$, $g : \mathbb{R} \to \mathbb{R}^m$, $x : \mathbb{R} \to \mathbb{R}^n$ and $y : \mathbb{R} \to \mathbb{R}^m$ (no regularity is required of $y$). Then the following are equivalent:

1. $x$ is differentiable and, for every $t$, $x'(t) = A x(t) + B y(t) + f(t)$ and $C x(t) + D y(t) + g(t) = 0$;
2. $x$ is differentiable and, for every $t$,

    $$x'(t) = (A - B D^{-1} C)\, x(t) + f(t) - B D^{-1} g(t), \qquad y(t) = -D^{-1}\bigl(C x(t) + g(t)\bigr).$$
