# Sign of a product of octonion basis elements

The eight-square multiplication table multiplies basis elements indexed by $\{0, 1\}^3$ as
$e_p e_q = \varepsilon(p, q)\, e_{p \oplus q}$, where $\oplus$ is bitwise exclusive or. For
$p = (p_1, p_2, p_3)$ and $q = (q_1, q_2, q_3)$ the sign is

$$\varepsilon(p, q) = (-1)^{p_1 q_1 + p_1 q_2 + p_1 q_3 + p_2 q_2 + p_2 q_3 + p_3 q_3 + q_1 p_2 p_3 + p_1 q_2 p_3 + p_1 p_2 q_3}.$$

An index $p$ is identified with the number $p_1 + 2 p_2 + 4 p_3$, so that $p_1$, $p_2$, $p_3$ are its
binary digits from the least significant.
