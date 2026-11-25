# Sojourn density of the Wright–Fisher diffusion with selection

For real numbers $\sigma$, $p$ and $x$, let

$$\Psi_\sigma(p, x) = \frac{2\, u_\sigma(\min(p, x))\, \bigl(1 - u_\sigma(\max(p, x))\bigr)}{x(1 - x)\, K_\sigma\, e^{-2\sigma x}},$$

where $u_\sigma$ is [Kimura's fixation probability](../wright-fisher-diffusion/kimura-fixation.md), $K_\sigma$ its [slope constant](../wright-fisher-diffusion/kimura-slope.md) (so the denominator is $x(1 - x)\,u_\sigma'(x)$), and division by $0$ gives $0$. In terms of the scale function $S(y) = (1 - e^{-2\sigma y})/(2\sigma)$ ($S(y) = y$ if $\sigma = 0$) it is $2 S(\min(p, x)) (S(1) - S(\max(p, x)))/(S(1)\, x(1 - x)\, e^{-2\sigma x})$. For $0 \le p \le 1$ and $0 < x < 1$, $\Psi_\sigma(p, x)\,dx$ is the expected time that an allele started at frequency $p$ spends in $(x, x + dx)$ before loss or fixation, in the Wright–Fisher diffusion with genic selection, with time in units of $2N$ generations and $\sigma = 2Ns$.

## Sources

- W. J. Ewens, *Mathematical Population Genetics I: Theoretical Introduction*, 2nd ed., Springer (2004).
