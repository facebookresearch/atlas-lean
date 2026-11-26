# Acyclic chains of encrypted secret keys

For a public-key bit-encryption scheme $\mathcal{E}$ and a depth $L$, an *acyclic key chain* consists of $L + 1$ independently generated key pairs $(pk_0, sk_0), \dots, (pk_L, sk_L)$ together with the $L$ *links* $\overline{sk_{i}} = \mathrm{Enc}(pk_{i+1}, sk_i)$ (bitwise), encrypting each secret key under the next public key. The public chain is $(pk_0, \dots, pk_L, \overline{sk_0}, \dots, \overline{sk_{L-1}})$. A chain is valid when each link is a supported encryption of the corresponding secret; a valid chain has one fewer link than key pairs.

## Depends on

- [CPA security of public-key encryption families](../../../security-games/asymptotic-security/pub-cpasecure.md)

## Sources

- Craig Gentry, "Fully Homomorphic Encryption Using Ideal Lattices", Proceedings of the Forty-First Annual ACM Symposium on Theory of Computing, 2009.
