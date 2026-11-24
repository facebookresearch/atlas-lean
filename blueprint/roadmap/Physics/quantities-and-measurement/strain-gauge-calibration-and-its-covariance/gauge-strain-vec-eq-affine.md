# The strain vector is an affine function of the voltage vector

For gains $g_1, \dots, g_n$, all nonzero, and offsets $b = (b_1, \dots, b_n)$, the
[strain vector](gauge-strain-vec.md) of a voltage vector $V \in \mathbb{R}^n$ is

$$
\varepsilon = D\,V - D\,b, \qquad D = \operatorname{diag}(1/g_1, \dots, 1/g_n),
$$

that is, $\varepsilon_i = V_i/g_i - b_i/g_i$ for each channel $i$. Since every gain is nonzero, $D$
is the inverse of $\operatorname{diag}(g_1, \dots, g_n)$.
