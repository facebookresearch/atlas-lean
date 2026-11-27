# CKKS rescaling divides message and error by the scale

Let $\mathbf{c}$ encrypt $m$ at level $\ell$ with error bound $B$ and $q_\ell/q_{\ell-1}=p$. Then $\mathrm{RS}(\mathbf{c})=\lfloor\mathbf{c}/p\rceil\bmod q_{\ell-1}$ encrypts $m/p$ at level $\ell-1$ with error bound $B/p+B_{\mathrm{rs}}$, where $B_{\mathrm{rs}}$ bounds the canonical norm of $\langle\boldsymbol{\rho},(1,s)\rangle$ for the rounding error $\boldsymbol{\rho}$ (coefficients in $[-1/2,1/2]$); with high probability $B_{\mathrm{rs}}=O(\sqrt{Nh})$ under the standard heuristic that rounding errors behave like independent uniform variables.

## Proof sketch

Write $b+as=m+e+q_\ell k$. Dividing by $p$ and rounding, $\lfloor b/p\rceil+\lfloor a/p\rceil s=(m+e)/p+q_{\ell-1}k-\langle\boldsymbol{\rho},(1,s)\rangle$. The rounding term $\rho_0+\rho_1s$ has canonical-embedding coordinates that are sums of about $h$ bounded independent terms plus one, giving $O(\sqrt{Nh})$ with high probability, or at most $(1+h)N/2$ deterministically.

## Depends on

- [CKKS ciphertexts and approximate decryption](ckks-ciphertexts.md)
- [CKKS encoding via the canonical embedding](canonical-embedding-encoding.md)

## Sources

- Jung Hee Cheon, Andrey Kim, Miran Kim, Yongsoo Song, "Homomorphic Encryption for Arithmetic of Approximate Numbers", ASIACRYPT (2017), IACR ePrint 2016/421.
