# Kurepa's partial integral

For a natural number $n$ and a real number $x$, Kurepa's partial
integral is

$$K_n(x) = \int_0^x e^{-t} \sum_{k=0}^{n-1} t^k \, dt,$$

an oriented integral, so for $x < 0$ it is minus the integral over $[x, 0]$.

The paper writes it as $!n(x) = \int_0^x e^{-t} \frac{t^n - 1}{t - 1} \, dt$; the geometric sum
agrees with $\frac{t^n - 1}{t - 1}$ for $t \ne 1$, and the singularity at $t = 1$ is removable.

## Sources

- Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio, Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024), Article 24.5.7, Section 1 (the function `!z(x)`) and Sections 3.1-3.3.
