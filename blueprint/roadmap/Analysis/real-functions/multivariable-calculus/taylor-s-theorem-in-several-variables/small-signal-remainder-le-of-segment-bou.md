# Remainder bound from a second-derivative bound along the segment

Let $n \in \mathbb{N}$, $i : \mathbb{R}^n \to \mathbb{R}$ and $v_0, dv \in \mathbb{R}^n$. If $i$ is
differentiable at $v_0$, the [restriction](segment-pullback.md) $g(t) = i(v_0 + t\,dv)$ is twice
continuously differentiable on $\mathbb{R}$, and $|g''(t)| \le M \|dv\|^2$ for every $t \in [0, 1]$,
with the sup norm $\|dv\| = \max_j |dv_j|$, then the [remainder](small-signal-remainder.md)
$r = i(v_0 + dv) - i(v_0) - Di(v_0)[dv]$ satisfies $|r| \le M \|dv\|^2 / 2$. Only the bound is local
to the segment; no hypothesis on $i$ away from $v_0$ is made beyond the smoothness of $g$.
