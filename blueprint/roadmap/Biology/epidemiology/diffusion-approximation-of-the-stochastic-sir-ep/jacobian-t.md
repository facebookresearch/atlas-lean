# Transposed Jacobian of the SIR drift

For real $\beta$, $\gamma$, $p = (s, i)$ and $y \in \mathbb{R}^2$, the transposed Jacobian of the
drift is

$$
DF(p)^{\mathsf T} y = \bigl(-\beta i y_1 + \beta i y_2,\quad
-\beta s y_1 + (\beta s - \gamma) y_2\bigr),
$$

so that $\langle y, DF(p)\, h \rangle = \langle DF(p)^{\mathsf T} y, h \rangle$ for the
[dot product](dot.md) and the [Jacobian](jacobian.md).
