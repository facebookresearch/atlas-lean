# The linear candidate solves the unclamped feedback equation

For real numbers $A > 0$, $\beta > 0$ and $v_i$, the [linear candidate](linear-candidate.md)
$c = A v_i/(1 + A\beta)$ satisfies $c = A(v_i - \beta c)$. Positivity of $A$ and $\beta$ ensures
$1 + A\beta \ne 0$; when $1 + A\beta = 0$ the candidate is $0$ by the convention $x/0 = 0$, and it
solves the equation only if $A v_i = 0$.

For the finite-gain feedback amplifier with $A, \beta > 0$ this says that the closed form
$v_o = A v_i/(1 + A\beta)$ solves the amplifier equation $v_o = A(v_i - \beta v_o)$ for every input;
by the [closed form of every solution](../feedback-amplifier-with-finite-gain/eq-closed-form-of-eq.md)
it is the only solution.
