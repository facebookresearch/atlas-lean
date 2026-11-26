# For ordered rails, values at or above $v_{\max}$ clamp to $v_{\max}$

For real numbers $v_{\min} \le v_{\max}$ and $x \ge v_{\max}$, the [rail clamp](rail-clamp.md) gives
$\operatorname{clamp}(v_{\min}, v_{\max}, x) = v_{\max}$. The ordering matters: for
$v_{\min} > v_{\max}$ the clamp gives $v_{\min}$.
