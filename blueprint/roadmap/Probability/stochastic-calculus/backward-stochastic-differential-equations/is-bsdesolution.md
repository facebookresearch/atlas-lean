# Solution of a one-dimensional BSDE on $[0, T]$

Let $(\Omega, P)$ be a probability space with a filtration $F$, $B$ a real process, $T \ge 0$, a generator
$g : [0, \infty) \times \Omega \times \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ and a terminal value
$\xi : \Omega \to \mathbb{R}$. A pair of real processes $(Y, Z)$ solves the BSDE with generator $g$ and
terminal value $\xi$ if

1. $Y$ and $Z$ are $F$-progressive;
2. $\mathbb E \int_0^T Y_t^2\, dt < \infty$ and $\mathbb E \int_0^T Z_t^2\, dt < \infty$ (the space $M^2(0, T)$);
3. almost surely, $s \mapsto g(s, Y_s, Z_s)$ is integrable on $[0, T]$;
4. for every $t \in [0, T]$, almost surely,

    $$Y_t = \xi + \int_t^T g(s, Y_s, Z_s)\, ds - \Bigl( \int_0^T Z\, dB - \int_0^t Z\, dB \Bigr),$$

    where $\int_0^t Z\, dB$ is the [$L^2$ Itô integral](../it-integral/ito-integral-2.md).

Condition 3 makes the drift integral a genuine Lebesgue integral on every $[t, T]$. This is Peng's
equation (1.7) with $m = d = 1$.

## Sources

- S. Peng, *Backward stochastic differential equation, nonlinear expectation and their applications*, Proceedings of the International Congress of Mathematicians 2010, Vol. I, Hindustan Book Agency, 2010, 393–432, Section 1.2, equation (1.7) and Theorem 1.1.
