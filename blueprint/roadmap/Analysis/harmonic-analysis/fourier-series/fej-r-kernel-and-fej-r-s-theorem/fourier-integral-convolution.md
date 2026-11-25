# Convolution of a function with a Fourier character

Let $T > 0$, let
$f : \mathbb{R}/T\mathbb{Z} \to \mathbb{C}$ be integrable with respect to the Haar probability
measure $dt$ on the circle, for $n \in \mathbb{Z}$ let $e_n(x) = e^{2\pi i n x / T}$ be the
$n$-th Fourier character, and let $\hat f(n) = \int_{\mathbb{R}/T\mathbb{Z}} e_{-n}(t)\, f(t)\, dt$
be the $n$-th Fourier coefficient of $f$. Then for every $n \in \mathbb{Z}$ and every
$x \in \mathbb{R}/T\mathbb{Z}$,

$$\int_{\mathbb{R}/T\mathbb{Z}} e_n(t)\, f(x - t)\, dt = \hat f(n)\, e_n(x).$$

Thus the $n$-th term of the partial Fourier sum of $f$ at $x$ is the convolution of $f$ with
the Fourier character $e_n$.
