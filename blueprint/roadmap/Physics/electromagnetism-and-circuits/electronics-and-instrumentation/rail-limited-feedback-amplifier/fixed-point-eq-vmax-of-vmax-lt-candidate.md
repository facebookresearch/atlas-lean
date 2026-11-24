# For A, β > 0, a candidate above the upper rail pins the output there

Let $A > 0$, $\beta > 0$ and $v_i$ be real numbers and $v_{\min} < v_{\max}$ the rails, and let
$v_o$ be a fixed point, $v_o = F(v_o)$, of the [rail-limited feedback map](rail-limited-map.md)
$F(v) = \operatorname{clamp}(v_{\min}, v_{\max}, A(v_i - \beta v))$. If the
[linear candidate](linear-candidate.md) satisfies $A v_i/(1 + A\beta) > v_{\max}$, then
$v_o = v_{\max}$: the output saturates at the upper rail.
