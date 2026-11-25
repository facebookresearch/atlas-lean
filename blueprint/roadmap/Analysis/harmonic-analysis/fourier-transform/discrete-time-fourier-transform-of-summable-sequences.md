# Discrete-time Fourier transform of absolutely summable sequences

For $x \in \ell^1(\mathbb{Z}; \mathbb{C})$, that is $\sum_{n \in \mathbb{Z}} |x_n| < \infty$, define its discrete-time Fourier transform

$$X(\nu) = \sum_{n \in \mathbb{Z}} x_n\, e^{-2\pi i \nu n} \qquad (\nu \in \mathbb{R}).$$

1. **Existence and continuity.** The series converges absolutely and uniformly in $\nu$, with $|X(\nu)| \le \|x\|_1$. The function $X$ is continuous and $1$-periodic, and as a function on $\mathbb{R}/\mathbb{Z}$ it lies in the Wiener algebra.
2. **Coefficients and inversion.** For every $n \in \mathbb{Z}$,

    $$x_n = \int_0^1 X(\nu)\, e^{2\pi i \nu n}\, d\nu ,$$

    so the $n$-th Fourier coefficient $\hat X(n) = \int_0^1 X(\nu) e^{-2\pi i n \nu}\, d\nu$ of $X$ is $x_{-n}$. In particular $x$ is determined by $X$.

3. **Convolution.** If $h, x \in \ell^1(\mathbb{Z}; \mathbb{C})$, then $h * x \in \ell^1(\mathbb{Z}; \mathbb{C})$, with $(h * x)_n = \sum_{k} h_k x_{n-k}$, and the transform of $h * x$ is $H(\nu) X(\nu)$ for every $\nu$.

In angular frequency $\omega = 2\pi\nu$ this is the source's $X(e^{i\omega}) = \sum_n x_n e^{-i\omega n}$, $2\pi$-periodic, with inversion $x_n = \frac{1}{2\pi} \int_{-\pi}^{\pi} X(e^{i\omega}) e^{i\omega n}\, d\omega$.

Part 1 follows from $|x_n e^{-2\pi i \nu n}| = |x_n|$, so the partial sums converge uniformly. Part 2 integrates the uniformly convergent series term by term, using $\int_0^1 e^{2\pi i \nu (n - k)}\, d\nu = \delta_{nk}$. Part 3 interchanges the two absolutely convergent sums in $\sum_n \sum_k h_k x_{n-k} e^{-2\pi i \nu n}$.

## Depends on

- [Wiener algebra on the circle](../fourier-series/absolutely-convergent-fourier-series/in-wiener-algebra.md): the class of continuous periodic functions with absolutely summable Fourier coefficients
- [Convolution of sequences on the integers](../../banach-spaces/sequence-spaces/convolution-on-p/int-conv.md): the convolution $h * x$ of part 3

## Proof depends on

- [Summability of convolution terms for $\ell^1$ and $\ell^p$ sequences](../../banach-spaces/sequence-spaces/convolution-on-p/summable-int-conv-term.md): the convolution series converges for $\ell^1$ sequences
- [Young's inequality with one $\ell^1$ factor](../../banach-spaces/sequence-spaces/convolution-on-p/norm-l1-conv-le.md): $h * x$ is again in $\ell^1$, with $\|h * x\|_1 \le \|h\|_1 \|x\|_1$
- [Pointwise formula for $\ell^1$–$\ell^p$ convolution](../../banach-spaces/sequence-spaces/convolution-on-p/l1-conv-apply.md): the $\ell^1$ convolution of Young's inequality has the values $(h * x)_n = \sum_k h_k x_{n-k}$

## Sources

- M. Vetterli, J. Kovačević and V. K. Goyal, *Foundations of Signal Processing*, Cambridge University Press, 2014 (free version v1.1), <https://fourierandwavelets.org/FSP_v1.1_2014.pdf>, Section 3.4: Definition of the DTFT (3.80a)–(3.80b), Section 3.4.2 (sequences in $\ell^1(\mathbb{Z})$: absolute convergence, continuity and the inversion computation (3.82a)–(3.82b), pp. 218–219), and Section 3.4.3, the convolution property (3.96)–(3.97) (p. 224).
