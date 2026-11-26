# Linear candidate $A v_i / (1 + A\beta)$ for the closed-loop output

For real numbers $A$, $\beta$ and $v_i$, the linear candidate is

$$c = \frac{A v_i}{1 + A\beta},$$

the closed-form candidate for the closed-loop output when the rails are ignored. The formula is
defined for all real inputs; with the convention $x/0 = 0$ it gives $c = 0$ when $1 + A\beta = 0$.

For $A > 0$ and $\beta > 0$, $c$ [solves the unclamped feedback equation](linear-candidate-satisfies.md)
$v_o = A(v_i - \beta v_o)$. If moreover $v_{\min} < v_{\max}$ and $c$ lies in
$[v_{\min}, v_{\max}]$, every fixed point of the [rail-limited map](rail-limited-map.md) equals $c$
([linear region](eq-linear-candidate-of-mem.md)).
