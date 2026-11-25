# Bilinear polynomial ergodic averages

Let $X$ be a measurable space and let
$T : X \to X$ be a measurable bijection with measurable inverse. For a real number $N \ge 0$,
polynomials $P_1, P_2 \in \mathbb{Z}[t]$, functions $f, g : X \to \mathbb{C}$ and a point
$x \in X$, the bilinear average is the complex number

$$A_N^{P_1, P_2}(f, g)(x) = \frac{1}{\lfloor N \rfloor}
\sum_{n=1}^{\lfloor N \rfloor} f(T^{P_1(n)} x)\, g(T^{P_2(n)} x),$$

where $T^k$ for $k \in \mathbb{Z}$ is the $k$-th power of $T$ in the group of bijections of $X$
(so negative powers are iterates of $T^{-1}$), and $A_N^{P_1, P_2}(f, g)(x) = 0$ when
$\lfloor N \rfloor = 0$.
