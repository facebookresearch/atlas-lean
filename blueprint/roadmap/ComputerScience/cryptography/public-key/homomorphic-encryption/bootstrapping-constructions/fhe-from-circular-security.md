# Fully homomorphic encryption from a circular-secure bootstrappable scheme

Let $\mathcal{E}$ be bootstrappable for the identity and NAND gates, with efficient algorithms and uniformly generated decryption circuits. In the *fixed-key* scheme, key generation samples one key pair $(pk, sk)$ and publishes $pk$ together with the self-encryption $\overline{sk} = \mathrm{Enc}(pk, sk)$ (bitwise); every circuit layer is evaluated by refresh and NAND refresh with this one artifact. Then the fixed-key scheme is perfectly correct and compact for every finite Boolean circuit, without a depth parameter in key generation. If moreover $\mathcal{E}$ is *circular secure*, meaning that $(pk, \overline{sk})$ is computationally indistinguishable from $(pk, \mathrm{Enc}(pk, 0^{|sk|}))$, and IND-CPA secure, then the fixed-key scheme is IND-CPA secure even against adversaries that choose their messages after seeing the encrypted secret. Hence a circular-secure bootstrappable scheme yields a fully homomorphic encryption scheme.

## Proof sketch

Correctness reuses the same supported key and self-encrypted secret at every layer, which only needs pointwise support, not independent randomness. For security, circular security replaces $\overline{sk}$ by an encryption of zero; then the public artifact can be generated from $pk$ alone and the remaining experiment is a base IND-CPA experiment.

## Depends on

- [Gentry's bootstrapping theorem](../gentry-s-bootstrapping-theorem.md)
- [Circular security from fully composable homomorphic encryption](../../circular-security-from-composable-homomorphic-encryption.md)
- [CPA security of public-key encryption families](../../../security-games/asymptotic-security/pub-cpasecure.md)

## Proof depends on

- [Correctness of refresh and NAND refresh](refresh-correctness.md)
- [Homomorphic evaluation of Boolean circuits layer by layer along a key chain](layered-circuit-evaluation.md)

## Sources

- Craig Gentry, "Fully Homomorphic Encryption Using Ideal Lattices", Proceedings of the Forty-First Annual ACM Symposium on Theory of Computing, 2009.
- Craig Gentry, "A Fully Homomorphic Encryption Scheme", 2009.
