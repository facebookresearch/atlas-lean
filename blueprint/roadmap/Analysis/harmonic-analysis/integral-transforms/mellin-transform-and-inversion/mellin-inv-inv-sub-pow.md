# Inverse Mellin transform of `(s − a)^{−m}`

Let `m ≥ 2` be an integer and let `a < σ` be
real numbers. For `x > 0`, with `x^{-s} = e^{-s \log x}`, the integral

$$I(x) = \int_{\sigma-i\infty}^{\sigma+i\infty} x^{-s}(s-a)^{-m}\,\frac{ds}{2\pi i}
  = \frac{1}{2\pi}\int_{-\infty}^{\infty} x^{-\sigma-it}(\sigma-a+it)^{-m}\,dt$$

converges absolutely, does not depend on `σ > a`, and

$$I(x) = \frac{x^{-a}\,|\log x|^{m-1}}{(m-1)!}\quad (0 < x \le 1), \qquad
  I(x) = 0 \quad (x \ge 1),$$

the two values agreeing at `x = 1` since `m ≥ 2`.

Here `I(x)` is Mathlib's `mellinInv σ (fun s => ((s - a) ^ m)⁻¹) x`. The conjuncts are, in order:
absolute convergence, independence of `σ`, the value on `(0, 1]`, the value on `[1, ∞)`, and the
vanishing of the first formula at `x = 1`.

## Sources

- J. Oesterlé, *Nombres de classes des corps quadratiques imaginaires*, Séminaire Bourbaki exposé 631, Astérisque 121–122 (1985), 309–323, §3.3, Lemme 1 and the sentence after it (p. 315).
