# Partial Fourier sums

Let $T > 0$ and $f : \mathbb{R}/T\mathbb{Z} \to \mathbb{C}$. For
$N \in \mathbb{N}$, the $N$-th partial Fourier sum of $f$ is the function

$$S_N f(x) = \sum_{n=-N}^{N} \hat f(n)\, e_n(x),$$

where $e_n(x) = e^{2\pi i n x / T}$ is the $n$-th Fourier character and
$\hat f(n) = \int_{\mathbb{R}/T\mathbb{Z}} e_{-n}(t)\, f(t)\, dt$ is the $n$-th Fourier coefficient,
the integral taken against the Haar probability measure on the circle.
