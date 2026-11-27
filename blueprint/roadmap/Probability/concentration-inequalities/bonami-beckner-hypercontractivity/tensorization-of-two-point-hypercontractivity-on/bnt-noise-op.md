# Noise operator on the Boolean cube

For a finite set $\iota$, $\rho \in \mathbb{R}$ and $f : \{0, 1\}^\iota \to \mathbb{R}$,
$T_\rho f(x) = \sum_{y} K_\rho(x, y)\, f(y)$, with the [noise kernel](bnt-noise-kernel.md)
$K_\rho$. For $\rho \in [-1, 1]$ it is the expectation of $f(y)$ when each coordinate of $y$
independently equals that of $x$ with probability $(1 + \rho)/2$.
