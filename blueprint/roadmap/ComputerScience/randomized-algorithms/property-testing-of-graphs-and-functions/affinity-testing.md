# Affinity testing and its Fourier formula

A Boolean function $f : \{0,1\}^n \to \{0,1\}$ is *affine* if $f = b \oplus \chi_S$ for some $S$ and bit $b$, equivalently $f(x) \oplus f(y) \oplus f(z) = f(x \oplus y \oplus z)$ for all $x, y, z$. The four-query affinity test checks this identity at uniform independent $x, y, z$; reading $F = (-1)^f$, its acceptance probability is

$$\frac12 + \frac12 \sum_{S} \hat F(S)^4.$$

Hence it accepts affine functions with probability $1$, and acceptance probability $1 - \varepsilon$ implies that $f$ is within relative distance $\varepsilon$ of an affine function.

## Proof sketch

Expand $\mathbb{E}[F(x)F(y)F(z)F(x\oplus y\oplus z)]$ in the Fourier basis; orthogonality leaves $\sum_S \hat F(S)^4 \le \max_S \hat F(S)^2$, and a large coefficient means closeness to $\pm\chi_S$.

## Depends on

- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)
- [Relative Hamming distance on the Boolean cube](../../../TheoryOfComputation/pcp-and-inapproximability/blum-luby-rubinfeld-linearity-test/bool-dist.md)
- [Blum–Luby–Rubinfeld linearity test](../../../TheoryOfComputation/pcp-and-inapproximability/blum-luby-rubinfeld-linearity-test/blr-test.md)

## Proof depends on

- [Parseval's identity on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/expect-sq-eq-sum-bool-fourier-coeff-sq.md)
- [Plancherel's identity on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/expect-mul-eq-sum-bool-fourier-coeff-mul.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
- M. Blum, M. Luby and R. Rubinfeld, "Self-Testing/Correcting with Applications to Numerical Problems", Journal of Computer and System Sciences 47(3), 1993.
