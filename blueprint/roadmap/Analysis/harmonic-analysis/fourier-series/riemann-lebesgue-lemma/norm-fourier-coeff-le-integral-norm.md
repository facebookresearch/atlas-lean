# A Fourier coefficient is bounded by the L¹ norm

Let $T > 0$, let $\mu$ be the Haar
probability measure on the circle $\mathbb{R}/T\mathbb{Z}$, and let $E$ be a normed space over
$\mathbb{C}$. For every function $f : \mathbb{R}/T\mathbb{Z} \to E$ and every $n \in \mathbb{Z}$,
the $n$-th Fourier coefficient $\hat f(n) = \int e^{-2\pi i n t / T} f(t)\,d\mu(t)$ satisfies
$\|\hat f(n)\| \le \int \|f(t)\|\,d\mu(t)$.

The bound holds because $|e^{-2\pi i n t / T}| = 1$. No integrability is assumed: as usual for
the Bochner integral, an integral whose integrand is not integrable is $0$, and so is any
$E$-valued integral when $E$ is not complete.
