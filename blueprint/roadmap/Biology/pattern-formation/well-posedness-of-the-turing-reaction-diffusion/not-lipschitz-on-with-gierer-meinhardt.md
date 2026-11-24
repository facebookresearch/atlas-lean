# The Gierer–Meinhardt kinetics are not Lipschitz on the unit ball

For all real $a$ and $b$ and every $L \ge 0$, the
[Gierer–Meinhardt kinetics](../turing-patterns-and-diffusion-driven-instability/gierer-meinhardt.md)
$(u, v) \mapsto (a - b u + u^2/v,\ u^2 - v)$, with $u^2/v$ read as $0$ when $v = 0$, are not
$L$-Lipschitz on the closed unit ball $\{(u, v) : \max(|u|, |v|) \le 1\}$ of $\mathbb{R}^2$. The
term $u^2/v$ blows up as $v \to 0^+$ at $u = 1$.

So these kinetics are not $C^1$ on $\mathbb{R}^2$ (a $C^1$ map on $\mathbb{R}^2$ is Lipschitz on
closed balls), and local well-posedness for $C^1$ kinetics does not apply to them. Applying it would
need an invariant region bounding $v$ away from $0$, or a cutoff of the kinetics.
