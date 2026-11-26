# Multilinear polynomial commitments from constrained Reed–Solomon proximity

Commit to a multilinear $\hat{f}$ in $m$ variables by a Merkle commitment to its Reed–Solomon encoding $f(x)=\hat{f}(\mathrm{pow}(x,m))$ on a smooth domain $L$. An evaluation claim $\hat{f}(z)=y$ for $z\in\mathbb{F}^{m}$ is exactly membership of the honestly encoded $f$ in $\mathrm{CRS}[\mathbb{F},L,m,\hat{w}_z,y]$ with $\hat{w}_z(Z,X)=Z\cdot\widetilde{\mathrm{eq}}(z,X)$, and a univariate claim at $x\in\mathbb{F}$ uses the point $\mathrm{pow}(x,m)$. An IOP of proximity for constrained Reed–Solomon codes that is round-by-round knowledge sound, such as WHIR, compiled with the BCS transformation in the random oracle model, therefore yields a multilinear (and univariate) polynomial commitment scheme; several claims form a multi-constrained code, which reduces to a single constraint. Two different statements must be kept apart. The Merkle root binds a prover only to some word $f:L\to\mathbb{F}$, not to a codeword, and the honest prover's word is an exact encoding. For an arbitrary committed word, proximity determines a unique polynomial only within the unique-decoding radius: if $f$ is $\delta$-close to the code with $\delta$ below half the minimum relative distance, there is exactly one codeword within $\delta$. Beyond that radius several codewords can be $\delta$-close to the same word, and the extractor must instead rely on WHIR's out-of-domain samples, which make two distinct codewords in the list agree on the sampled points only with small probability, together with its knowledge-sound compiler.

## Proof sketch

The sum $\sum_b\hat{f}(b)\widetilde{\mathrm{eq}}(z,b)$ equals $\hat{f}(z)$ by the equality-polynomial identity. Within the unique-decoding radius, two codewords $\delta$-close to $f$ would be closer than the minimum distance, hence equal. Beyond it, round-by-round knowledge soundness of the IOP of proximity, with out-of-domain sampling bounding the probability that two list elements agree on the samples by the list size and the field size, and Merkle extraction in the random oracle model yield an extractor for a polynomial consistent with the claims.

## Depends on

- [Constrained Reed–Solomon codes with sum-check constraints](constrained-rs-code.md)
- [Polynomial commitment schemes](../zero-knowledge-and-arguments/polynomial-commitment-schemes.md)
- [Merkle root](../../hash-functions/merkle-trees/root.md)
- [The multilinear equality polynomial on the Boolean hypercube](../plonkish-polynomial-iops/eq-polynomial.md)
- [Interactive oracle proofs of proximity for Reed–Solomon codes](rs-iopp.md)

## Proof depends on

- [Existential soundness of Merkle inclusion proofs](../../hash-functions/merkle-trees/verify-sound.md)
- [Out-of-domain sampling pins down a unique list-decoded codeword](out-of-domain-sampling.md)

## Sources

- Gal Arnon, Alessandro Chiesa, Giacomo Fenzi, Eylon Yogev, "WHIR: Reed–Solomon Proximity Testing with Super-Fast Verification", EUROCRYPT (2025), IACR ePrint 2024/1586, Section 1 (hash-based polynomial commitments from constrained Reed–Solomon codes), Section 4.4 (Lemmas 4.24 and 4.25), Section 6.3.3 and Section 7.
