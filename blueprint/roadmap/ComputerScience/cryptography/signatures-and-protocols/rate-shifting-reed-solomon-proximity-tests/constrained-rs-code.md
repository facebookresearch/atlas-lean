# Constrained Reed–Solomon codes with sum-check constraints

Let $m\ge 1$, $L\subseteq\mathbb{F}$ with $|L|\ge 2^{m}$, and identify a polynomial $\hat{f}$ of degree $< 2^{m}$ with the multilinear polynomial $\bar{f}(X_1,\dots,X_m)$ having the same coefficient vector, so that $\hat{f}(x)=\bar{f}(x,x^{2},x^{4},\dots,x^{2^{m-1}})$. Given a weight polynomial $\hat{w}\in\mathbb{F}[Z,X_1,\dots,X_m]$ and a target $\sigma\in\mathbb{F}$, the *constrained Reed–Solomon code* $\mathrm{CRS}[\mathbb{F},L,m,\hat{w},\sigma]$ consists of the codewords $f\in\mathrm{RS}[\mathbb{F},L,2^{m}]$ such that

$$
\sum_{b\in\{0,1\}^{m}}\hat{w}\bigl(\bar{f}(b),b\bigr)=\sigma.
$$

With $\hat{w}(Z,X)=Z\cdot\widetilde{\mathrm{eq}}(z,X)$ the constraint states $\bar{f}(z)=\sigma$, a multilinear evaluation claim; with $\hat{w}(Z,X)=Z\cdot\prod_i(1+(x^{2^{i-1}}-1)X_i)$ for a point $x$ it states $\hat{f}(x)=\sigma$.

## Depends on

- [Interactive oracle proofs of proximity for Reed–Solomon codes](rs-iopp.md)
- [The multilinear equality polynomial on the Boolean hypercube](../plonkish-polynomial-iops/eq-polynomial.md)

## Sources

- Gal Arnon, Alessandro Chiesa, Giacomo Fenzi, Eylon Yogev, "WHIR: Reed–Solomon Proximity Testing with Super-Fast Verification", EUROCRYPT (2025), IACR ePrint 2024/1586.
