# Partially hiding FE for degree-two private computations from SXDH

Assuming the SXDH assumption in asymmetric bilinear groups of prime order $p$, there is a partially hiding functional encryption scheme for functions that are arbitrary constant-degree (polynomial-size arithmetic) functions of the public input and degree at most $2$ in the private input, with ciphertext size $O(|\mathbf{y}|)\cdot\mathrm{poly}(\lambda)$ group elements plus the public input, secure against adversaries obtaining one key, where decryption recovers $f(\mathbf{x},\mathbf{y})$ in the target group (and in $\mathbb{Z}_p$ when the output is small, via discrete logarithm over a polynomial range).

## Proof sketch

Encrypt $\mathbf{y}$ entrywise in $\mathbb{G}_1$ and $\mathbb{G}_2$ with function-hiding inner-product-style randomness so that a pairing of the two encodings yields the degree-2 monomials masked by terms the key can cancel; coefficients depending on $\mathbf{x}$ are absorbed into the key-side computation since $\mathbf{x}$ is public. Security follows from DDH in each source group by hybrid arguments on the random masks.

## Depends on

- [Partially hiding functional encryption for degree-two private computations](partially-hiding-fe.md)
- [The symmetric external Diffie–Hellman assumption](../obfuscation-from-well-founded-assumptions/sxdh-assumption.md)
- [Bilinear groups](../../advanced-encryption-and-pairings/bilinear-groups.md)

## Sources

- Aayush Jain, Huijia Lin, Amit Sahai, "Indistinguishability Obfuscation from Well-Founded Assumptions", STOC (2021), IACR ePrint 2020/1003, arXiv:2008.09317.
