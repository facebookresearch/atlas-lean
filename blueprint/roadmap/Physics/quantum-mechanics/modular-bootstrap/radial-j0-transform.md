# Planar radial Fourier transform in the shifted-dimension variable

Use the planar Fourier convention $\widehat f(y)=\int_{\mathbb R^2} f(r)e^{-2\pi i r\cdot y}\,d^2r$. For $f(r)=g(|r|^2/2)$ put $t=|r|^2/2$ and $s=|y|^2/2$. If $\int_0^\infty|g(t)|\,dt<\infty$, the radial formula for real $s\ge0$ is

$$
\widehat g(s)=2\pi\int_0^\infty g(t)J_0(4\pi\sqrt{st})\,dt,
\qquad J_0(z)=\sum_{k=0}^\infty\frac{(-1)^k(z^2/4)^k}{(k!)^2}.
$$

In particular, $e^{-2\pi\beta t}$ transforms to $\beta^{-1}e^{-2\pi s/\beta}$ for $\beta>0$. The combination $e^{-2\pi\beta t}-\beta^{-1}e^{-2\pi t/\beta}$ is odd for this transform. The radial Fourier plane has dimension two for every $c$ in the Virasoro problem.

## Expansion

Use polar coordinates and the angular integral for $J_0$ to match the radial integral with the two-dimensional Fourier transform. Prove agreement of the real kernel with the order-zero first-kind Bessel series, including at zero, and use Fourier inversion only on the domains where its hypotheses hold. To continue in $s$, use the series in $st$, not a branch choice of $\sqrt{s}$.

## Sources

- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [§2.3, (2.8)–(2.10), p. 10](https://hexagonmath.org/pdf/2611.00174v1#page=10).
