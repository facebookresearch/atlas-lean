# Loaded DC gain is $a$ times the closed-loop gain of $b A_0$

For all real numbers $A_0$, $\beta$, $a$, $b$, the [loaded DC gain](loaded-dc-gain.md) factors as

$$
\frac{a b A_0}{1 + \beta b A_0} = a \cdot G(b A_0, \beta), \qquad
G(A, \beta) = \frac{A}{1 + A\beta},
$$

where $G$ is the [closed-loop gain](closed-loop-gain.md) of the finite-gain feedback amplifier.
Both sides have the denominator $1 + \beta b A_0 = 1 + (b A_0)\,\beta$, so the identity holds for
every input, including $1 + \beta b A_0 = 0$, where both sides are $0$ by the convention
$x / 0 = 0$. In the model, $a$ is the [source divider](source-divider.md) and $b A_0$ is the
open-loop gain referred to the load through the [load divider](load-divider.md) $b$: the loaded DC
gain is the source divider times the closed-loop gain of the load-referred open-loop gain.
