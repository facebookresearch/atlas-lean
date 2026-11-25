# Linear candidate $A v_i / (1 + A\beta)$ for the closed-loop output

For real numbers $A$, $\beta$ and $v_i$, the linear candidate is

$$c = \frac{A v_i}{1 + A\beta},$$

the closed-loop output given by the feedback equation $v_o = A(v_i - \beta v_o)$ when the rails are
ignored. Whenever $1 + A\beta \ne 0$, in particular for $A > 0$ and $\beta > 0$, it is the unique
solution of that linear equation. The formula is defined for all real inputs, with the convention
$x/0 = 0$: when $1 + A\beta = 0$ it gives $c = 0$, although the equation then has no solution unless
$A v_i = 0$.
