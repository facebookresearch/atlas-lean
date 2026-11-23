# Harmonic numbers from binomial coefficients

For every $N \in \mathbb{N}$,

$$\sum_{j=1}^{N} \binom{N}{j} \frac{(j - 1)!\, (N - j)!}{N!} = H_N = \sum_{j=1}^{N} \frac1j.$$

Grouping the $2^N - 1$ non-zero histories by their number of ones $j$, this is the sum over histories of the rates $(m_h - 1)!\,(N - m_h)!/N!$, which produces the factor $e^{-\alpha H_N}$ of Equation 14.

## Sources

- Thomas L. Griffiths and Zoubin Ghahramani, *The Indian buffet process: an introduction and review*, J. Mach. Learn. Res. 12 (2011), 1185–1224, Equation 16, second equality.
