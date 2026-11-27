# Level-1 inequality for [−1, 1]-valued functions

For every $f : \{-1,1\}^n \to [-1, 1]$ with $\alpha = \mathbb{E}|f| \le 1/2$,

$$\mathbf{W}^1[f] \le 16\,\alpha^2\ln\frac{1}{\alpha},$$

with the right side read as $0$ when $\alpha = 0$ (then $f = 0$).

## Proof sketch

Let $\sigma = \sqrt{\mathbf{W}^1[f]}$; assume $\sigma > 0$. The normalized degree-one part $\ell = f^{=1}/\sigma$ has $\|\ell\|_2 = 1$ and $\sigma = \mathbb{E}[f\ell]$. For $s \ge 1$ split according to whether $|\ell| \le s$: the small part contributes at most $s\,\mathbb{E}|f| = s\alpha$, and since $|f| \le 1$ the large part is at most $\mathbb{E}[\mathbf{1}\{|\ell| > s\}|\ell|] \le (2 + 2s)e^{-s^2/2} \le 4s e^{-s^2/2}$ by the subgaussian (Hoeffding) tail of a Rademacher linear form (O'Donnell, Lemma 5.31). Taking $s = \sqrt{2\ln(16/\alpha)}$ gives $\sigma \le \frac54\alpha s$, so $\mathbf{W}^1[f] \le \frac{25}{8}\alpha^2\big(\ln\frac1\alpha + \ln 16\big) \le 16\,\alpha^2\ln\frac1\alpha$, using $\ln 16 = 4\ln 2 \le 4\ln(1/\alpha)$.

## Depends on

- [Fourier weight at each degree](../fourier-expansion-supplements/fourier-weight-at-each-degree.md)
- [Level-1 Inequality](../structure-theorems-for-boolean-functions/level-one-inequality.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
