# Sequence components are the normalized DFT of the phases at the negated frequency

For $V_a, V_b, V_c \in \mathbb{C}$ and $\alpha = e^{2\pi i/3}$, the symmetrical components are
$V_0 = (V_a + V_b + V_c)/3$, $V_1 = (V_a + \alpha V_b + \alpha^2 V_c)/3$ and
$V_2 = (V_a + \alpha^2 V_b + \alpha V_c)/3$, forming the [sequence array](sequence-vector.md)
$(V_0, V_1, V_2)$. Index the phases by $\mathbb{Z}/3$ as $v_0 = V_a$, $v_1 = V_b$, $v_2 = V_c$ (the
[phase array](phase-vector.md)), and let $\hat v$ be their normalized discrete Fourier transform,
with a negative exponent:

$$\hat v(k) = \frac{1}{3} \sum_{j \in \mathbb{Z}/3} e^{-2\pi i jk/3}\, v_j.$$

Then for every $s \in \mathbb{Z}/3$ the $s$-th component of $(V_0, V_1, V_2)$ is $\hat v(-s)$; that
is, $(V_0, V_1, V_2) = (\hat v(0), \hat v(2), \hat v(1))$.

Equivalently, $(V_0, V_1, V_2)$ is the inverse discrete Fourier transform of the phase array:
$V_s = \frac{1}{3} \sum_{j \in \mathbb{Z}/3} e^{2\pi i js/3}\, v_j$ for every $s \in \mathbb{Z}/3$.
