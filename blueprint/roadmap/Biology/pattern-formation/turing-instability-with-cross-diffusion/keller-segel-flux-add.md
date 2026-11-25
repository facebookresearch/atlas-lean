# Linearization of the chemotactic flux

For real $d_u$, $d_v$, $\chi$, a state $s = (s_0, s_1)$, a perturbation $p = (p_0, p_1)$ and a
gradient $g = (g_0, g_1)$, the [Keller–Segel flux](keller-segel-flux.md) at the state $s + p$ is

$$D(s_0)\, g + (-\chi\, p_0\, g_1,\ 0),$$

where $D(s_0) = \begin{pmatrix} d_u & -\chi s_0 \\ 0 & d_v \end{pmatrix}$ is the
[linearized diffusion matrix](keller-segel-diffusion.md). The remainder is bilinear in $p$ and $g$,
so the system linearized at a homogeneous state $s$ has diffusion matrix $D(s_0)$.
