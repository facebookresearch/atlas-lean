# A band-limited spectrum is the Fourier series of the samples

Let $f$ be a Schwartz function whose Fourier transform $\hat f(\xi) = \int f(x) e^{-2\pi i x \xi}\,dx$ vanishes outside $[-\tfrac12, \tfrac12]$. Then for every $\xi \in (-\tfrac12, \tfrac12)$,

$$\hat f(\xi) = \sum_{n \in \mathbb{Z}} f(n)\, e^{-2\pi i n \xi} .$$

Poisson's summation formula for the Schwartz function $\hat f$ gives $\sum_m \hat f(\xi + m) = \sum_n \mathcal{F}\hat f(n)\, e^{2\pi i n \xi}$; on $(-\tfrac12, \tfrac12)$ only the term $m = 0$ survives, and $\mathcal{F}\hat f(n) = f(-n)$. This is the step of Shannon's proof in which the samples $f(n/2W)$ are recognized as the Fourier coefficients of the spectrum on $[-W, W]$ (C. E. Shannon, *Communication in the presence of noise*, Proc. IRE 37 (1949), proof of Theorem 1), here with $W = 1/2$.
