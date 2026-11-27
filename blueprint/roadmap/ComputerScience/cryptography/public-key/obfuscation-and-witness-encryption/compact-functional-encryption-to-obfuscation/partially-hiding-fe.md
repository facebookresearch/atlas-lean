# Partially hiding functional encryption for degree-two private computations

A *partially hiding functional encryption* scheme for a class of functions $f(\mathbf{x},\mathbf{y})$, with public input $\mathbf{x}\in\mathbb{Z}_p^{n_{\mathrm{pub}}}$ and private input $\mathbf{y}\in\mathbb{Z}_p^{n_{\mathrm{priv}}}$, encrypts $(\mathbf{x},\mathbf{y})$ revealing $\mathbf{x}$ in the clear, and a key for $f$ decrypts to $f(\mathbf{x},\mathbf{y})$; security requires that ciphertexts of $(\mathbf{x},\mathbf{y}_0)$ and $(\mathbf{x},\mathbf{y}_1)$ are indistinguishable given keys for functions $f$ with $f(\mathbf{x},\mathbf{y}_0)=f(\mathbf{x},\mathbf{y}_1)$. The relevant class has $f$ computable by constant-depth ($\mathsf{NC}^{0}$-type) circuits in $\mathbf{x}$ and of degree at most $2$ in $\mathbf{y}$, and the key efficiency requirement is that the ciphertext size is linear in $|\mathbf{y}|$ (and independent of the output length) up to $\mathrm{poly}(\lambda)$ factors.

## Depends on

- [Single-key weakly compact public-key functional encryption](weakly-compact-fe.md)
- [Bilinear groups](../../advanced-encryption-and-pairings/bilinear-groups.md)

## Sources

- Aayush Jain, Huijia Lin, Amit Sahai, "Indistinguishability Obfuscation from Well-Founded Assumptions", STOC (2021), IACR ePrint 2020/1003, arXiv:2008.09317.
- Huijia Lin, Stefano Tessaro, "Indistinguishability Obfuscation from Trilinear Maps and Block-Wise Local PRGs", CRYPTO (2017).
