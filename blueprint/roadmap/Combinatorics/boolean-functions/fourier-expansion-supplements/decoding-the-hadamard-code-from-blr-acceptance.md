# Decoding the Hadamard code from BLR acceptance

If $f : \mathbb{F}_2^n \to \mathbb{F}_2$ passes the BLR test with probability at least $1 - \varepsilon$, then there is $a \in \mathbb{F}_2^n$ such that $f$ is within relative distance $\varepsilon$ of the Hadamard codeword $x \mapsto \langle a, x \rangle$; if $\varepsilon < 1/4$ this codeword is unique, since distinct Hadamard codewords are at distance $1/2$. Conversely, a function at relative distance $\delta$ from all parities is rejected with probability at least $\delta$.

## Proof sketch

BLR acceptance equals $\frac12 + \frac12\sum_S \hat F(S)^3 \le \frac12 + \frac12 \max_S \hat F(S)$, so some $\hat F(S) \ge 1 - 2\varepsilon$, i.e. $f$ agrees with $\chi_S$ on a $1 - \varepsilon$ fraction. Uniqueness follows from the triangle inequality.

## Depends on

- [Blum–Luby–Rubinfeld linearity test](../../../TheoryOfComputation/pcp-and-inapproximability/blum-luby-rubinfeld-linearity-test/blr-test.md)
- [Relative Hamming distance on the Boolean cube](../../../TheoryOfComputation/pcp-and-inapproximability/blum-luby-rubinfeld-linearity-test/bool-dist.md)
- [Local decoding of the Hadamard code](../../../InformationTheory/error-correcting-codes/hadamard-code-local-decoding.md)

## Proof depends on

- [Acceptance probability of the BLR test in Fourier form](../../../TheoryOfComputation/pcp-and-inapproximability/blum-luby-rubinfeld-linearity-test/blr-accept-prob-eq.md)

## Sources

- M. Blum, M. Luby and R. Rubinfeld, "Self-Testing/Correcting with Applications to Numerical Problems", Journal of Computer and System Sciences 47(3), 1993.
- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
