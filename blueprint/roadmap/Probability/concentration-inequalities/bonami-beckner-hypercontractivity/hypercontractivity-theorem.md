# Hypercontractivity Theorem (Bonami–Beckner)

Let $f : \{-1, 1\}^n \to \mathbb{R}$ and $1 \le p \le q < \infty$. Then

$$\|T_\rho f\|_q \le \|f\|_p \qquad\text{for}\quad 0 \le \rho \le \sqrt{\frac{p - 1}{q - 1}},$$

where $T_\rho$ is the noise operator and $\|g\|_r = (\mathbb{E}|g|^r)^{1/r}$ under the uniform
measure. For $p = q = 1$ the quotient $0/0$ is read as $0$, so that case covers only $\rho = 0$. The source also allows $q = \infty$, which the statement above omits.

## Sources

- A. Bonami (1970); W. Beckner, "Inequalities in Fourier analysis", *Ann. of Math.* 102 (1975),
  159–182.
- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014 (arXiv:2105.10386), The Hypercontractivity Theorem, introduction of Chapter 9; proved in Chapter 10.

## Background

- [Tensorization of two-point hypercontractivity on the uniform cube](tensorization-of-two-point-hypercontractivity-on/README.md):
  the induction on the dimension by which two-point inequalities give the theorem on
  $\{-1, 1\}^n$, here carried out for $q = 2$.
- [The two-point Bonami inequality](the-two-point-bonami-inequality/README.md): the one-bit
  inequality from which the induction starts.
