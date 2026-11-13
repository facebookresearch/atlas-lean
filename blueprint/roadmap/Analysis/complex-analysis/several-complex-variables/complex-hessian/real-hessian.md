# Real Hessian

For a function $u : \mathbb{C}^n \to \mathbb{R}$, with $\mathbb{C}^n$
viewed as a real normed space, write $Du(w)$ for the real Fréchet derivative of $u$ at $w$. For
points $z, a, b \in \mathbb{C}^n$, the real Hessian $D^2u(z)(a, b)$ is the real number obtained
by taking the real Fréchet derivative at $z$ of the map $w \mapsto Du(w)$, applying it to $a$,
and applying the result to $b$.

As usual in Mathlib, a derivative that does not exist is taken to be zero.
