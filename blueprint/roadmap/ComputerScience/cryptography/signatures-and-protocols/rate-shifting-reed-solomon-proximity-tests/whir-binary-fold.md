# Binary folding of multilinear-coefficient codewords as partial evaluation

For $\hat{f}$ of degree $< 2^{m}$ with multilinear form $\bar{f}$, and $\alpha\in\mathbb{F}$, write $\hat{f}(X)=\hat{f}_0(X^{2})+X\hat{f}_1(X^{2})$ and set $\mathrm{Fold}(\hat{f},\alpha)=\hat{f}_0+\alpha\hat{f}_1$. Then the multilinear form of $\mathrm{Fold}(\hat{f},\alpha)$ is $\bar{f}(\alpha,X_2,\dots,X_m)$, and for $x\in L$ with $-x\in L$ and $\mathrm{char}\,\mathbb{F}\ne 2$,

$$
\mathrm{Fold}(f,\alpha)(x^{2})=\frac{f(x)+f(-x)}{2}+\alpha\cdot\frac{f(x)-f(-x)}{2x}.
$$

Hence $m$ rounds of folding with challenges $\alpha_1,\dots,\alpha_m$ leave the constant $\bar{f}(\alpha_1,\dots,\alpha_m)$, linking proximity testing to sum-check over the hypercube.

## Proof sketch

The coefficient of $X^{2i}$ in $\hat{f}$ is the coefficient of the monomial with $X_1$-exponent $0$ in $\bar{f}$ and that of $X^{2i+1}$ has $X_1$-exponent $1$; combining with $\alpha$ substitutes $X_1=\alpha$. The displayed formula solves $f(\pm x)=\hat{f}_0(x^{2})\pm x\hat{f}_1(x^{2})$ for $\hat{f}_0,\hat{f}_1$.

## Depends on

- [Constrained Reed–Solomon codes with sum-check constraints](constrained-rs-code.md)

## Proof depends on

- [k-wise folding of Reed–Solomon codewords reduces degree](rs-folding-operator.md)

## Sources

- Gal Arnon, Alessandro Chiesa, Giacomo Fenzi, Eylon Yogev, "WHIR: Reed–Solomon Proximity Testing with Super-Fast Verification", EUROCRYPT (2025), IACR ePrint 2024/1586.
