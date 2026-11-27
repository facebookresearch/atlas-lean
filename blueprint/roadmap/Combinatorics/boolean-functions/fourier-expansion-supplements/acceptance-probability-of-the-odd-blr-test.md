# Acceptance probability of the Odd BLR test

For $f : \mathbb{F}_2^n \to \mathbb{F}_2$ read as $F = (-1)^f$, the *Odd BLR test* picks $x, y$ uniformly and a uniform bit $b$, and accepts iff $f(x) + f(y) + f(x + y + (b, \dots, b)) = b$. It accepts with probability

$$\frac12 + \frac12 \sum_{|S| \text{ odd}} \hat F(S)^3,$$

hence with probability at most $\frac12 + \frac12 M$ for every $M \ge 0$ with $\hat F(S) \le M$ for all odd $|S|$. (The bound with $M = \max_{|S|\text{ odd}}\hat F(S)$ fails when that maximum is negative: the NAND of two bits has odd coefficients $-1/2$ and passes with probability $3/8$.) An honest long-code word is a coordinate projection $f(x) = x_i$, so $F = \chi_{\{i\}}$ has its only nonzero coefficient, $+1$, on a singleton and passes with probability $1$; this is why the test underlies Håstad's 3-bit PCPs. Oddness alone does not suffice: the odd table $F = -\chi_{\{i\}}$ passes with probability $0$.

## Proof sketch

Averaging over $b$ projects onto odd characters: $\mathbb{E}_b[(-1)^b \chi_S(\mathbf{b})] = [|S| \text{ odd}]$. The remaining expectation $\mathbb{E}[F(x)F(y)F(x+y+\mathbf{b})]$ expands to $\sum_S \hat F(S)^3 \chi_S(\mathbf b)$ by orthogonality, as in the BLR analysis; then bound $\sum_{|S|\text{ odd}} \hat F(S)^3 \le M\sum_S \hat F(S)^2 = M$.

## Depends on

- [Blum–Luby–Rubinfeld linearity test](../../../TheoryOfComputation/pcp-and-inapproximability/blum-luby-rubinfeld-linearity-test/blr-test.md)
- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)

## Proof depends on

- [Acceptance probability of the BLR test in Fourier form](../../../TheoryOfComputation/pcp-and-inapproximability/blum-luby-rubinfeld-linearity-test/blr-accept-prob-eq.md)
- [Parseval's identity on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/expect-sq-eq-sum-bool-fourier-coeff-sq.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
- J. Håstad, "Some Optimal Inapproximability Results", Journal of the ACM 48(4), 2001.
