# Fourier spectrum of the inner product mod 2

Let $\mathrm{IP}_{2n}(x, y) = (-1)^{\langle x, y\rangle}$ for $x, y \in \mathbb{F}_2^n$, viewed as a function on $2n$ bits. For every set $S$ of coordinates, with $S_x, S_y \in \mathbb{F}_2^n$ the indicator vectors of the parts of $S$ in the two halves,

$$\widehat{\mathrm{IP}_{2n}}(S) = \frac{(-1)^{\langle S_x, S_y\rangle}}{2^n},$$

so every Fourier coefficient has absolute value $2^{-n}$ and the spectrum is flat. Consequently $\mathrm{IP}$ is a bent function, it has correlation at most $2^{-n}$ with every parity, and every monochromatic rectangle of $\mathrm{IP}$ has at most $2^n$ entries.

## Proof sketch

Summing $(-1)^{\langle x,y\rangle + \langle a, x\rangle + \langle b, y\rangle}$ first over $y$ forces $x = b$, leaving $2^n (-1)^{\langle a, b\rangle}$, divided by $4^n$.

## Depends on

- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
