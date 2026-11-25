# With negative feedback, there is exactly one fixed point

For real numbers $A > 0$, $\beta > 0$ and $v_i$ and rails $v_{\min} < v_{\max}$, the equation

$$v_o = \operatorname{clamp}(v_{\min}, v_{\max}, A(v_i - \beta v_o))$$

has exactly one real solution $v_o$: the [rail-limited feedback map](rail-limited-map.md) has a
unique fixed point.
