# Constrained Reed–Solomon codes with sum-check constraints

Let $m\ge1$ and let $L\subseteq\mathbb{F}$ be a smooth evaluation domain: a multiplicative coset of $\mathbb{F}^{*}$ whose order is a power of two, with $|L|\ge2^{m}$. For $x\in\mathbb{F}$ write $\mathrm{pow}(x,m)=(x,x^{2},x^{4},\dots,x^{2^{m-1}})$. The smooth Reed–Solomon code $\mathrm{RS}[\mathbb{F},L,m]$ consists of the functions $f:L\to\mathbb{F}$ that are evaluations of a univariate polynomial of degree $<2^{m}$, equivalently of the form $f(x)=\hat{f}(\mathrm{pow}(x,m))$ for a multilinear $\hat{f}\in\mathbb{F}[X_1,\dots,X_m]$ (the multilinear polynomial with the same coefficient vector); its rate is $2^{m}/|L|$. Given a weight polynomial $\hat{w}\in\mathbb{F}[Z,X_1,\dots,X_m]$ and a target $\sigma\in\mathbb{F}$, the *constrained Reed–Solomon code* $\mathrm{CRS}[\mathbb{F},L,m,\hat{w},\sigma]$ consists of the codewords $f\in\mathrm{RS}[\mathbb{F},L,m]$ such that

$$
\sum_{b\in\{0,1\}^{m}}\hat{w}\bigl(\hat{f}(b),b\bigr)=\sigma.
$$

With $\hat{w}(Z,X)=Z\cdot\widetilde{\mathrm{eq}}(z,X)$ for $z\in\mathbb{F}^{m}$ the constraint states $\hat{f}(z)=\sigma$, a multilinear evaluation claim. With $\hat{w}(Z,X)=Z\cdot\widetilde{\mathrm{eq}}(\mathrm{pow}(x,m),X)$ for $x\in\mathbb{F}$ it states that the univariate polynomial underlying $f$ takes the value $\sigma$ at $x$, because a multilinear polynomial equals its own multilinear extension: $\hat{f}(\mathrm{pow}(x,m))=\sum_b\widetilde{\mathrm{eq}}(\mathrm{pow}(x,m),b)\hat{f}(b)$.

## Depends on

- [Interactive oracle proofs of proximity for Reed–Solomon codes](rs-iopp.md)
- [The multilinear equality polynomial on the Boolean hypercube](../plonkish-polynomial-iops/eq-polynomial.md)

## Sources

- Gal Arnon, Alessandro Chiesa, Giacomo Fenzi, Eylon Yogev, "WHIR: Reed–Solomon Proximity Testing with Super-Fast Verification", EUROCRYPT (2025), IACR ePrint 2024/1586, Section 1 and Section 4.1 (Definitions 4.2 and 4.5).
