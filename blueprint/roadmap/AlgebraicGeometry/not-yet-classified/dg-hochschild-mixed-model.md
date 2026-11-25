# The Hochschild mixed complex of a DG algebra

For a commutative ring $k$ and a DG algebra
$A$ over $k$: a cochain complex $C$ whose degree-$r$ term is identified with
$\bigoplus_{n \ge 0} (A^{\otimes (n+1)})^{r+n}$, with differential $(-1)^n d$ (the internal
differential of $A^{\otimes (n+1)}$) plus the alternating sum $\sum_i (-1)^i d_i$ of the bar faces,
together with a cochain $B$ of degree $-1$ on $C$ satisfying $dB + Bd = 0$ and $B^2 = 0$, given on
the summands by Connes' operator $(1 - t)\,s\,N$, where $t = (-1)^n \tau$ is the signed cyclic
rotation, $N = 1 + t + \dots + t^n$ and $s$ inserts the unit in front
(`HochschildMixedModel A`).
