# For ordered rails, every fixed point lies in the rail interval

Let $A$, $\beta$ and $v_i$ be real numbers and $v_{\min} \le v_{\max}$. If $v_o = F(v_o)$ for the
[rail-limited feedback map](rail-limited-map.md)
$F(v) = \operatorname{clamp}(v_{\min}, v_{\max}, A(v_i - \beta v))$, then
$v_{\min} \le v_o \le v_{\max}$, because the clamp takes its values in that interval. No condition
on $A$ or $\beta$ is needed.
