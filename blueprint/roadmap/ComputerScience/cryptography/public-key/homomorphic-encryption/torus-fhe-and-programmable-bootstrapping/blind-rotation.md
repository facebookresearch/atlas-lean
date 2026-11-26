# Blind rotation of a test polynomial by an encrypted phase

Let $(\mathbf{a},b)$ be a TLWE sample under $\mathbf{s}\in\{0,1\}^{n}$ and let $\bar{a}_i=\lfloor 2Na_i\rceil$, $\bar{b}=\lfloor 2Nb\rceil$, so that $\bar{\varphi}=\bar{b}-\sum_i\bar{a}_is_i\bmod 2N$ approximates $2N\varphi$. Given bootstrapping keys $\mathrm{BK}_i$, TRGSW samples of $s_i$, and a test polynomial $v\in\mathbb{T}_N[X]$, set $\mathrm{ACC}_0=(\mathbf{0},X^{-\bar{b}}v)$ and $\mathrm{ACC}_i=\mathrm{CMux}(\mathrm{BK}_i,X^{\bar{a}_i}\mathrm{ACC}_{i-1},\mathrm{ACC}_{i-1})$. Then $\mathrm{ACC}_n$ is a TRLWE sample of $X^{-\bar{\varphi}}\cdot v$, with error variance at most $n\bigl((k+1)\ell N\beta^{2}\vartheta_{\mathrm{BK}}+(1+kN)\epsilon^{2}\bigr)$, independent of the input sample's error.

## Proof sketch

By induction, $\mathrm{ACC}_i$ encrypts $X^{-\bar{b}+\sum_{j\le i}\bar{a}_js_j}v$: the CMux selects multiplication by $X^{\bar{a}_i}$ exactly when $s_i=1$, and multiplication by a monomial is a noiseless rotation of a TRLWE sample. Since $X^{2N}=1$ in $\mathbb{T}_N[X]$, exponents live in $\mathbb{Z}_{2N}$. Each CMux adds the stated external-product noise, and the initial accumulator is noiseless.

## Depends on

- [The homomorphic multiplexer CMux](cmux-gate.md)
- [TLWE and TRLWE samples over the real torus](tlwe-samples.md)
- [TRGSW samples and the gadget decomposition](trgsw-samples.md)

## Sources

- Ilaria Chillotti, Nicolas Gama, Mariya Georgieva, Malika Izabachène, "TFHE: Fast Fully Homomorphic Encryption over the Torus", Journal of Cryptology (2020), IACR ePrint 2018/421.
- Léo Ducas, Daniele Micciancio, "FHEW: Bootstrapping Homomorphic Encryption in Less than a Second", EUROCRYPT (2015), IACR ePrint 2014/816.
