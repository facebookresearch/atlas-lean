# Approximate correctness of CKKS homomorphic evaluation

Let $f$ be an arithmetic circuit over $\mathbb{C}$ of multiplicative depth $L'\le L$ with addition, multiplication and slot-rotation gates, applied slotwise to $\mathbf{z}_1,\dots,\mathbf{z}_k\in\mathbb{C}^{N/2}$, and evaluate it with CKKS using scale $\Delta$, rescaling by $p=\Delta$ after every multiplication. For each gate $g$ let $M_g$ bound the absolute values of the exact slot values at $g$, and define error bounds $B_g$ recursively: $B_g=B_{\mathrm{fresh}}+N/2$ at an input, $B_g=B_{g_1}+B_{g_2}$ at an addition, $B_g=B_{g_1}+B_{\mathrm{ks}}$ at a rotation, and

$$
B_g=\frac{\Delta M_{g_1}B_{g_2}+\Delta M_{g_2}B_{g_1}+B_{g_1}B_{g_2}+B_{\mathrm{ks}}}{\Delta}+B_{\mathrm{rs}}
$$

at a multiplication, where $B_{\mathrm{fresh}}$, $B_{\mathrm{ks}}$, $B_{\mathrm{rs}}$ bound the canonical norms of fresh-encryption, key-switching and rescaling errors. Then every gate's ciphertext encrypts $\Delta\,\tau^{-1}(\text{exact slot values})$ with error bound $B_g$, provided no reduction modulo the current $q_\ell$ wraps around; in particular the decoded output $\mathbf{w}$ at level $L-L'$ satisfies $\|\mathbf{w}-f(\mathbf{z}_1,\dots,\mathbf{z}_k)\|_\infty\le B_{\mathrm{out}}/\Delta$. This correctness statement is unconditional; IND-CPA security of the scheme rests on Ring-LWE together with circular security of the relinearization and rotation keys.

## Proof sketch

Induct over the circuit. An encryption of $\mathrm{Ecd}(\mathbf{z})$ is an encryption of $\Delta\tau^{-1}(\mathbf{z})$ whose error absorbs the encoding rounding, of canonical norm at most $N/2$; additions add errors; rotations add a key-switching error; and the multiplication-error lemma with $\nu_i=\Delta M_{g_i}$ and $p=\Delta$ gives the multiplication rule. Decoding divides by $\Delta$.

## Depends on

- [CKKS encoding via the canonical embedding](canonical-embedding-encoding.md)
- [CKKS ciphertexts and approximate decryption](ckks-ciphertexts.md)

## Proof depends on

- [Error propagation of CKKS multiplication with relinearization and rescaling](ckks-multiplication-error.md)
- [Rounding error of CKKS encoding](ckks-encoding-error.md)
- [Galois automorphisms rotate plaintext slots](../leveled-packed-fhe-bgv-and-bfv/galois-slot-rotations.md)

## Sources

- Jung Hee Cheon, Andrey Kim, Miran Kim, Yongsoo Song, "Homomorphic Encryption for Arithmetic of Approximate Numbers", ASIACRYPT (2017), IACR ePrint 2016/421.
