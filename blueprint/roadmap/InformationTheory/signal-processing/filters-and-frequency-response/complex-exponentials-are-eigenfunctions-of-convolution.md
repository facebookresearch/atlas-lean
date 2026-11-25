# Complex exponentials are eigenfunctions of convolution; the moving-average filter

1. **Discrete time.** Let $h \in \ell^1(\mathbb{Z}; \mathbb{C})$ have discrete-time Fourier transform $H(\nu) = \sum_k h_k e^{-2\pi i \nu k}$. For every $\nu \in \mathbb{R}$, the convolution of $h$ with $e_\nu(n) = e^{2\pi i \nu n}$ converges absolutely and

    $$(h * e_\nu)(n) = \sum_{k \in \mathbb{Z}} h_k\, e^{2\pi i \nu (n - k)} = H(\nu)\, e^{2\pi i \nu n} \qquad (n \in \mathbb{Z}).$$

2. **Continuous time.** Let $h \in L^1(\mathbb{R}; \mathbb{C})$ have Fourier transform $\hat h(f) = \int h(\tau) e^{-2\pi i f \tau}\, d\tau$. For every $f \in \mathbb{R}$, the integral $(h * e_f)(t) = \int h(\tau) e^{2\pi i f (t - \tau)}\, d\tau$ converges absolutely and equals $\hat h(f)\, e^{2\pi i f t}$ for every $t \in \mathbb{R}$.
3. **Moving average.** For an integer $M \ge 1$, the causal $M$-tap moving average $h_k = 1/M$ for $0 \le k < M$, $h_k = 0$ otherwise, has

    $$H(\nu) = \frac{1}{M} \sum_{k=0}^{M-1} e^{-2\pi i \nu k}, \qquad |H(\nu)| = \left| \frac{\sin(\pi M \nu)}{M \sin(\pi \nu)} \right| \quad (\nu \notin \mathbb{Z}),$$

    with $H(\nu) = 1$ for $\nu \in \mathbb{Z}$. For $0 < \nu < 1$, $H(\nu) = 0$ exactly when $\nu = j/M$ with $0 < j < M$.

Parts 1 and 2 factor $e^{2\pi i \nu n}$ (resp. $e^{2\pi i f t}$) out of the sum (resp. integral), which converges absolutely because the exponential has modulus $1$. Part 3 sums a geometric series: for $\nu \notin \mathbb{Z}$, $\sum_{k<M} w^k = (1 - w^M)/(1 - w)$ with $w = e^{-2\pi i \nu} \ne 1$, and $|1 - e^{-i\theta}| = 2|\sin(\theta/2)|$.

## Depends on

- [Discrete-time Fourier transform of absolutely summable sequences](../../../Analysis/harmonic-analysis/fourier-transform/discrete-time-fourier-transform-of-summable-sequences.md): the transform $H$ of an absolutely summable sequence

## Sources

- M. Vetterli, J. Kovačević and V. K. Goyal, *Foundations of Signal Processing*, Cambridge University Press, 2014 (free version v1.1), <https://fourierandwavelets.org/FSP_v1.1_2014.pdf>, Section 3.4: the eigensequence property of complex exponential sequences (3.77) (p. 217) and Section 3.4.4, frequency response of filters (from p. 227), and Example 3.18, the moving-average filter (pp. 229–230), stated there for the centered filter of odd length $N$; for odd $M$ the causal filter above is that filter delayed by $(M - 1)/2$ samples and has the same $|H|$, and for every $M$ part 3 is the finite geometric sum computed above; Section 4.4.1: the eigenfunction property (4.38)–(4.39) for continuous-time convolution (p. 360).
