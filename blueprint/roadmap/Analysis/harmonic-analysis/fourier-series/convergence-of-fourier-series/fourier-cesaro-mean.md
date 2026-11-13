# Cesàro means of Fourier series

For $f \colon \mathbb{R} \to \mathbb{C}$, a natural number
$N$ and $x \in \mathbb{R}$, the $N$-th Cesàro mean of the Fourier series of $f$ at $x$ is the
average of the first $N + 1$ symmetric Fourier partial sums,
$\sigma_N(f)(x) = \frac{1}{N+1} \sum_{k=0}^{N} S_k(f)(x)$, where
$S_k(f)(x) = \sum_{n=-k}^{k} \hat f_n e^{inx}$ and
$\hat f_n = \frac{1}{2\pi} \int_0^{2\pi} e^{-int} f(t)\,dt$ is the $n$-th Fourier coefficient of
$f$ on the interval $[0, 2\pi]$.
