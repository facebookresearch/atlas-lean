# Error propagation of CKKS multiplication with relinearization and rescaling

Let $\mathbf{c}_i$ encrypt $m_i$ with $\|m_i\|^{\mathrm{can}}\le\nu_i$ and error bounds $B_i$ at level $\ell$. Then tensoring, relinearizing (with key-switching error bound $B_{\mathrm{ks}}$) and rescaling by $p$ yields an encryption of $m_1m_2/p$ at level $\ell-1$ with error bound

$$
\frac{\nu_1B_2+\nu_2B_1+B_1B_2+B_{\mathrm{ks}}}{p}+B_{\mathrm{rs}}.
$$

With $\nu_i\approx\Delta=p$ and $B_i\ll\Delta$, the relative error of the decoded product is about the sum of the input relative errors plus $(B_{\mathrm{ks}}/p+B_{\mathrm{rs}})/\Delta$, so precision decreases additively (logarithmically in bits) with multiplicative depth.

## Proof sketch

$(m_1+e_1)(m_2+e_2)=m_1m_2+m_1e_2+m_2e_1+e_1e_2$; bound each term with submultiplicativity of the canonical norm. Relinearization adds $B_{\mathrm{ks}}$, and the rescaling lemma divides by $p$ and adds $B_{\mathrm{rs}}$.

## Depends on

- [CKKS ciphertexts and approximate decryption](ckks-ciphertexts.md)
- [CKKS encoding via the canonical embedding](canonical-embedding-encoding.md)

## Proof depends on

- [CKKS rescaling divides message and error by the scale](ckks-rescaling.md)
- [Relinearization by gadget key switching](../leveled-packed-fhe-bgv-and-bfv/relinearization.md)

## Sources

- Jung Hee Cheon, Andrey Kim, Miran Kim, Yongsoo Song, "Homomorphic Encryption for Arithmetic of Approximate Numbers", ASIACRYPT (2017), IACR ePrint 2016/421.
