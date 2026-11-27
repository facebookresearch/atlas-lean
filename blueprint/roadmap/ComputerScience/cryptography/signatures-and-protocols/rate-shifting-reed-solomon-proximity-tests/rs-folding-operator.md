# k-wise folding of Reed–Solomon codewords reduces degree

Let $L$ be a multiplicative coset whose $k$-th powers form $L^{k}=\{x^{k}:x\in L\}$ with $|L^{k}|=|L|/k$. Every $\hat{f}$ of degree $< d$ decomposes uniquely as $\hat{f}(X)=\sum_{j=0}^{k-1}X^{j}\hat{f}_j(X^{k})$ with $\deg\hat{f}_j< d/k$. For $\alpha\in\mathbb{F}$ define $\mathrm{Fold}(\hat{f},\alpha)(Y)=\sum_{j< k}\alpha^{j}\hat{f}_j(Y)$. Then $\mathrm{Fold}(f,\alpha)$ evaluated on $L^{k}$ is computable from the $k$ values of $f$ on each fiber $\{x:x^{k}=y\}$ by solving a $k\times k$ Vandermonde system, and if $f$ is a codeword of $\mathrm{RS}[\mathbb{F},L,d]$ then $\mathrm{Fold}(f,\alpha)\in\mathrm{RS}[\mathbb{F},L^{k},d/k]$. Conversely, if $f$ is $\delta$-far from $\mathrm{RS}[\mathbb{F},L,d]$ with $\delta<1-\sqrt{\rho}$, then the fraction of $\alpha\in\mathbb{F}$ for which $\mathrm{Fold}(f,\alpha)$ is $\delta$-close to $\mathrm{RS}[\mathbb{F},L^{k},d/k]$ is at most the error $\varepsilon_{\mathrm{ca}}$ of the Ben-Sasson–Carmon–Ishai–Kopparty–Saraf correlated-agreement theorem for the degree-$(k-1)$ curve $\alpha\mapsto\sum_{j<k}\alpha^{j}f_j$ at distance $\delta$.

## Proof sketch

The decomposition groups monomials by exponent modulo $k$. On a fiber the values $f(x)=\sum_jx^{j}\hat{f}_j(y)$ form a Vandermonde system in the unknowns $\hat{f}_j(y)$, solvable since the fiber has $k$ distinct points. The converse uses correlated agreement for the $k$ functions $\hat{f}_j$ on $L^{k}$.

## Depends on

- [Interactive oracle proofs of proximity for Reed–Solomon codes](rs-iopp.md)

## Sources

- Eli Ben-Sasson, Iddo Bentov, Yinon Horesh, Michael Riabzev, "Fast Reed-Solomon Interactive Oracle Proofs of Proximity", ICALP (2018).
- Gal Arnon, Alessandro Chiesa, Giacomo Fenzi, Eylon Yogev, "STIR: Reed–Solomon Proximity Testing with Fewer Queries", CRYPTO (2024), IACR ePrint 2024/390.
- Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, Shubhangi Saraf, "Proximity Gaps for Reed–Solomon Codes", FOCS (2020), IACR ePrint 2020/654.
