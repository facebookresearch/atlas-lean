# Restoring IND-CPA-D security of CKKS by noise flooding decryptions

Run CKKS as a statically approximate scheme: each ciphertext $\mathsf{ct}$ carries a public upper bound $\mathsf{ct}.t$ on its error, computed from the circuit by an error-estimation procedure. Let $\text{S-CKKS}_\sigma$ be CKKS with decryption replaced by $\mathsf{Dec}_{sk}(\mathsf{ct})+N_{\mathbb{Z}^{n}}(0,\sigma^{2}(\mathsf{ct}.t)^{2}I_n)$, adding an independent discrete Gaussian vector to the decrypted integer vector of dimension $n$. For a budget of $q$ decryption queries, if CKKS is $(\kappa+8)$-bit IND-CPA secure and $\sigma=8\sqrt{qn}\,2^{\kappa/2}$, then $\text{S-CKKS}_\sigma$ is $\kappa$-bit secure in the $q$-query IND-CPA-D game, so about $\kappa/2+\log_2\sqrt{qn}+3$ extra bits of precision are lost. Under a relaxed notion of $(c,s)$-bit security, which separates the computational cost $c$ from the statistical term $s$, $\sigma=\sqrt{24qn}\,2^{s/2}$ suffices when CKKS is $(c+\log_2 24)$-bit IND-CPA secure. The noise distribution matters, not just its size: noise of large norm with disjoint translates, such as a point mass, gives no protection.

## Proof sketch

The discrete Gaussian mechanism $x\mapsto N_{\mathbb{Z}^{n}}(x,\tfrac{t^{2}}{2\rho}I_n)$ is $\rho$-KL differentially private for inputs within $\ell_2$ distance $t$, since the KL divergence between discrete Gaussians with the same parameter and centers $x,y$ is $\|x-y\|_2^{2}/(2\sigma^{2})$. In the IND-CPA-D game the decryption oracle only answers queries whose two plaintexts agree, and the two possible decryptions then differ by at most the static error bound; replacing each answer by the mechanism applied to the common plaintext costs KL divergence at most $\rho$ per query. A KL-based bit-security argument then reduces $q$-IND-CPA-D security with $\rho\le2^{-\kappa-7}/q$ to IND-CPA security, and the static bound in the canonical $\infty$-norm is converted to $\ell_2$ via $\|m\|_\infty^{\mathrm{can}}\le\sqrt{n}\,\|m\|_2$. The relaxed version uses a hybrid argument that bounds the statistical term $q\rho$ against IND-CPA security.

## Depends on

- [IND-CPA-D security for approximate homomorphic encryption](ind-cpa-d-security.md)
- [CKKS ciphertexts and approximate decryption](ckks-ciphertexts.md)
- [CKKS encoding via the canonical embedding](canonical-embedding-encoding.md)

## Proof depends on

- [Key recovery against CKKS from decryptions of honest ciphertexts](li-micciancio-key-recovery.md)

## Sources

- Baiyu Li, Daniele Micciancio, "On the Security of Homomorphic Encryption on Approximate Numbers", EUROCRYPT (2021), IACR ePrint 2020/1533.
- Baiyu Li, Daniele Micciancio, Mark Schultz, Jessica Sorrell, "Securing Approximate Homomorphic Encryption Using Differential Privacy", CRYPTO (2022), Theorems 3 and 5, Corollary 2.
