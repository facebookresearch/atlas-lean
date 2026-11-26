# Binary folding of multilinear-coefficient codewords as partial evaluation

Let $L$ be a smooth evaluation domain (a multiplicative coset of $\mathbb{F}^{*}$ of power-of-two order at least $2$, so that $0\notin L$, $-x\in L$ for every $x\in L$, and $\operatorname{char}\mathbb{F}\ne2$), and write $L^{(2)}=\{x^{2}:x\in L\}$. For $f:L\to\mathbb{F}$ and $\alpha\in\mathbb{F}$ define $\mathrm{Fold}(f,\alpha):L^{(2)}\to\mathbb{F}$ by

$$
\mathrm{Fold}(f,\alpha)(x^{2})=\frac{f(x)+f(-x)}{2}+\alpha\cdot\frac{f(x)-f(-x)}{2x}\qquad(x\in L),
$$

which is well defined because $x\ne0$ on $L$; on a domain containing $0$ the formula is undefined there. If $f\in\mathrm{RS}[\mathbb{F},L,m]$ with multilinear form $\hat{f}$, then $\mathrm{Fold}(f,\alpha)\in\mathrm{RS}[\mathbb{F},L^{(2)},m-1]$ and its multilinear form is $\hat{f}(\alpha,X_2,\dots,X_m)$. Hence $k\le m$ rounds of folding with challenges $\alpha_1,\dots,\alpha_k$ give a codeword with multilinear form $\hat{f}(\alpha_1,\dots,\alpha_k,X_{k+1},\dots,X_m)$, and $m$ rounds leave the constant $\hat{f}(\alpha_1,\dots,\alpha_m)$, linking proximity testing to sum-check over the hypercube.

## Proof sketch

Write $\hat{f}=\hat{f}_0(X_2,\dots,X_m)+X_1\hat{f}_1(X_2,\dots,X_m)$ and let $\mathbf{z}=\mathrm{pow}(x^{2},m-1)$. Since $\mathrm{pow}(\pm x,m)=(\pm x,\mathbf{z})$, we have $f(\pm x)=\hat{f}_0(\mathbf{z})\pm x\hat{f}_1(\mathbf{z})$; solving for $\hat{f}_0(\mathbf{z})$ and $\hat{f}_1(\mathbf{z})$, which requires dividing by $2$ and by $x$, shows that the displayed value is $\hat{f}_0(\mathbf{z})+\alpha\hat{f}_1(\mathbf{z})$, the multilinear form evaluated with $X_1=\alpha$. Induction on $k$ gives the iterated statement.

## Depends on

- [Constrained Reed–Solomon codes with sum-check constraints](constrained-rs-code.md)

## Proof depends on

- [k-wise folding of Reed–Solomon codewords reduces degree](rs-folding-operator.md)

## Sources

- Gal Arnon, Alessandro Chiesa, Giacomo Fenzi, Eylon Yogev, "WHIR: Reed–Solomon Proximity Testing with Super-Fast Verification", EUROCRYPT (2025), IACR ePrint 2024/1586, Section 4.3 (Definition 4.14 and Claim 4.15).
