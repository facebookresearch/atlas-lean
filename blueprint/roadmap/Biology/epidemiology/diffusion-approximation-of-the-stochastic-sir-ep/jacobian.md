# Jacobian of the SIR drift

For real $\beta$, $\gamma$, $p = (s, i)$ and $h = (h_1, h_2)$, the Jacobian of the [drift](drift.md)
at $p$ applied to $h$ is

$$DF(p)\, h = \bigl(-\beta (i h_1 + s h_2),\ \beta (i h_1 + s h_2) - \gamma h_2\bigr),$$

the matrix $\begin{pmatrix} -\beta i & -\beta s \\ \beta i & \beta s - \gamma \end{pmatrix}$ applied
to $h$.
