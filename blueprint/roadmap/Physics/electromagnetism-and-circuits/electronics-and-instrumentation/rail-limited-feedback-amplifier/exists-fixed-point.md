# Existence of a fixed point of the rail-limited map

For real numbers $A > 0$, $\beta > 0$ and $v_i$ and rails $v_{\min} < v_{\max}$, the
[rail-limited feedback map](rail-limited-map.md)
$F(v) = \operatorname{clamp}(v_{\min}, v_{\max}, A(v_i - \beta v))$ has a fixed point
$v_o = F(v_o)$, which lies in $[v_{\min}, v_{\max}]$
([every fixed point does](fixed-point-mem-icc.md)). The proof treats three regimes of the
[linear candidate](linear-candidate.md) $c = A v_i/(1 + A\beta)$: for $c < v_{\min}$ the rail
$v_{\min}$ is a fixed point, for $c > v_{\max}$ the rail $v_{\max}$ is, and otherwise $c$ is.
