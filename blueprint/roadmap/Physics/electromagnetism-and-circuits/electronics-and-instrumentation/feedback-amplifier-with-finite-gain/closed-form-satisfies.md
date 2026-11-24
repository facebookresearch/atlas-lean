# For $A, \beta > 0$ the closed form solves the amplifier equation

For real numbers $A > 0$ and $\beta > 0$ (the open-loop gain and the feedback factor) and every real
input $v_i$, the closed form $v_o = A v_i / (1 + A\beta)$ satisfies the amplifier equation
$v_o = A (v_i - \beta v_o)$ of the finite-gain feedback amplifier:

$$\frac{A\, v_i}{1 + A\beta} = A \left( v_i - \beta\, \frac{A\, v_i}{1 + A\beta} \right).$$

So for $A, \beta > 0$ the amplifier equation has a solution for every input; by the
[closed form of every solution](eq-closed-form-of-eq.md) it is the only one.
