# Reverse hypercontractivity of a single bit

For a nonnegative function $f$ of one uniform bit and a real $t \ne 0$ write $\|f\|_t = (\mathbb{E} f^t)^{1/t}$, where for $t < 0$ this is defined for positive $f$ and extended by its limit from positive functions, which is $0$ when $f$ vanishes somewhere. Let $q < p \le 1$ be finite and nonzero, and $0 \le \rho \le \sqrt{(1-p)/(1-q)}$. Then $\|f\|_p \le \|T_\rho f\|_q$ for every nonnegative $f$. Equivalently, for $a \ge |b|$ with $f(\pm1) = a \pm b$: $\big(\frac{(a+b)^p + (a-b)^p}{2}\big)^{1/p} \le \big(\frac{(a+\rho b)^q + (a - \rho b)^q}{2}\big)^{1/q}$, with the same conventions.

## Proof sketch

Following O'Donnell, Ex. 10.7. (a) For $0 < q < p \le 1$ and $\rho = \sqrt{(1-p)/(1-q)}$, normalize $a = 1$ and, for $|b| < 1$, compare the binomial series of both sides in $b$ term by term, as in the forward two-point inequality; $|b| = 1$ follows by continuity. (b) A smaller $\rho$ equals $\sqrt{(1-p')/(1-q)}$ for some $p' \in [p, 1]$, and $\|f\|_p \le \|f\|_{p'}$ by monotonicity of the norms in the exponent. (c) For $q < p < 0$ argue by duality with the reverse Hölder inequality. (d) For $q < 0 < p$ write $T_\rho$ as a composition $T_{\rho_1}T_{\rho_2}$ through the exponent $0$ (the geometric mean, a limit of the $t$-norms), using the one-signed cases on each side. Functions with zeros follow by the limit convention.

## Depends on

- [Noise operator on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-op.md)

## Proof depends on

- [L^p seminorms under a probability measure increase with the exponent](../fourier-expansion-supplements/lp-norms-increase-with-p.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
