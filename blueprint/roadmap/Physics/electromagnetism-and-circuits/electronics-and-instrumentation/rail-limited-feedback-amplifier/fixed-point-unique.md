# With negative feedback, there is at most one fixed point

For real numbers $A > 0$, $\beta > 0$ and $v_i$ and rails $v_{\min} < v_{\max}$, any two fixed
points $v_o = F(v_o)$ and $v_o' = F(v_o')$ of the [rail-limited feedback map](rail-limited-map.md)
$F(v) = \operatorname{clamp}(v_{\min}, v_{\max}, A(v_i - \beta v))$ are equal: $v \mapsto F(v) - v$
is strictly decreasing, since the clamped amplified error does not increase with $v$. The sign of
the feedback matters: for $A = 2$, $\beta = -1$, $v_i = 0$ and rails $[-1, 1]$, both $0$ and $1$ are
fixed points.
