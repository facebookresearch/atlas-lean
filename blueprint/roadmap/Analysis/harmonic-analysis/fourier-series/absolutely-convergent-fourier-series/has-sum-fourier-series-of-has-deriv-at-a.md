# Pointwise convergence on one period

For $T > 0$ and $g : \mathbb{R} \to \mathbb{C}$, write $\hat g(n) = \frac{1}{T} \int_0^T g(x)\, e^{-2\pi i n x/T}\, dx$, $n \in \mathbb{Z}$, for the Fourier coefficients of $g$ on the period $(0, T]$ (an integral whose integrand is not integrable being read as $0$). Let $T > 0$ and let $f, f' : \mathbb{R} \to \mathbb{C}$ be such that $f$ is $T$-periodic and differentiable at every point with derivative $f'$, with $f$ and $f'$ continuous. Then for every $x \in (0, T]$,

$$
\sum_{n \in \mathbb{Z}} \hat f(n)\, e^{2\pi i n x/T} = f(x),
$$

the series converging unconditionally.
