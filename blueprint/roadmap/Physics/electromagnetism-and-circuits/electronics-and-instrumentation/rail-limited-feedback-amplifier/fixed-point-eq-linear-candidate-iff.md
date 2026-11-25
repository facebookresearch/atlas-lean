# For A, β > 0, the candidate is the fixed point iff it is in the rails

Let $A > 0$, $\beta > 0$ and $v_i$ be real numbers and $v_{\min} < v_{\max}$ the rails, and let
$v_o$ be a fixed point, $v_o = F(v_o)$, of the [rail-limited feedback map](rail-limited-map.md)
$F(v) = \operatorname{clamp}(v_{\min}, v_{\max}, A(v_i - \beta v))$. Then $v_o = c$ if and only if
$v_{\min} \le c \le v_{\max}$, where $c = A v_i/(1 + A\beta)$ is the
[linear candidate](linear-candidate.md): the amplifier works in its linear region exactly when the
candidate lies in the closed rail interval.
