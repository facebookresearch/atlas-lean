# Restoring IND-CPA-D security of CKKS by noise flooding decryptions

If the CKKS decryption algorithm adds to $m+e$ an independent noise term of canonical norm larger than every possible evaluation error by a factor $2^{\kappa}$ (e.g., discrete Gaussian with suitable parameter), then the statistical distance between decryptions of any two ciphertexts with equal shadow plaintexts is at most $2^{-\Omega(\kappa)}$ per query, and the scheme is IND-CPA-D secure, with a precision loss of about $\kappa$ bits. With differential-privacy-calibrated Gaussian noise, the number of bits lost can be reduced to logarithmic in the number of decryption queries, at the cost of a security guarantee measured in terms of privacy loss over the queries.

## Proof sketch

Two decryptions differ only by their error terms, of norm at most the error bound $B$. Adding noise of width $2^{\kappa}B$ makes the two output distributions statistically close (the statistical distance of shifted Gaussians is proportional to the shift over the width). A hybrid over decryption queries gives IND-CPA-D from IND-CPA; differential-privacy composition yields the refined trade-off.

## Depends on

- [IND-CPA-D security for approximate homomorphic encryption](ind-cpa-d-security.md)
- [CKKS ciphertexts and approximate decryption](ckks-ciphertexts.md)
- [CKKS encoding via the canonical embedding](canonical-embedding-encoding.md)

## Proof depends on

- [Key recovery against CKKS from decryptions of honest ciphertexts](li-micciancio-key-recovery.md)

## Sources

- Baiyu Li, Daniele Micciancio, "On the Security of Homomorphic Encryption on Approximate Numbers", EUROCRYPT (2021), IACR ePrint 2020/1533.
- Baiyu Li, Daniele Micciancio, Mark Schultz, Jessica Sorrell, "Securing Approximate Homomorphic Encryption Using Differential Privacy", CRYPTO (2022).
