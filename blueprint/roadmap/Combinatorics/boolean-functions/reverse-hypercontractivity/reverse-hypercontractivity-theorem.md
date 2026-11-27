# Reverse hypercontractivity theorem on the cube

For a nonnegative function $f$ on $\{-1,1\}^n$ and a real $t \ne 0$ write $\|f\|_t = (\mathbb{E} f^t)^{1/t}$; for $t < 0$ this is defined for positive $f$ and extended to nonnegative $f$ by its limit from positive functions, which is $0$ when $f$ vanishes anywhere on the cube. For finite nonzero exponents $q < p \le 1$ and $0 \le \rho \le \sqrt{(1-p)/(1-q)}$, every nonnegative $f$ satisfies $\|f\|_p \le \|T_\rho f\|_q$. In two-function form: for nonnegative $f, g$, real $r, s \le 0$ with $r, s \ne -1$, $rs \le 1$ and $0 \le \rho \le \sqrt{rs}$, $\mathbb{E}[f(x)g(y)] \ge \|f\|_{1+r}\|g\|_{1+s}$ for $\rho$-correlated $(x,y)$. In particular, for $0 \le \rho \le 1/2$ and arbitrary real $f, g$, $(\mathbb{E}|f|)^2(\mathbb{E}|g|)^2 \le \mathbb{E}[f(x)^2 g(y)^2]$.

## Proof sketch

Following O'Donnell, Exs. 10.6–10.7: it suffices to treat positive functions, the limit convention handling zeros. The two forms are equivalent by the reverse Hölder inequality $\mathbb{E}[FG] \ge \|F\|_{1+r}\|G\|_{1+1/r}$ for positive $F, G$ and $r < 0$, and the two-function form tensorizes coordinate by coordinate as in the forward proof, reducing to one bit, where the reverse two-point inequality for all finite nonzero exponents applies. The last claim is the case $r = s = -1/2$ applied to $f^2$ and $g^2$, since $\|f^2\|_{1/2} = (\mathbb{E}|f|)^2$.

## Depends on

- [Noise operator on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-op.md)

## Proof depends on

- [Reverse hypercontractivity of a single bit](reverse-hypercontractivity-of-a-single-bit.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
