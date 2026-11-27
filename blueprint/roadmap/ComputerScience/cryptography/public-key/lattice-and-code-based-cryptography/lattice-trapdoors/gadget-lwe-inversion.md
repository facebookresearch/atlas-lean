# Efficient inversion of gadget LWE

Let $q = 2^w$ and $G = I_\ell \otimes g^{\mathsf T}$. There is a deterministic polynomial-time algorithm that, given $b^{\mathsf T} = s^{\mathsf T} G + e^{\mathsf T} \bmod q$ with $s \in \mathbb{Z}_q^\ell$ and an integer error vector $e$ all of whose coordinates satisfy $4|e_i| < q$, recovers $s$ (and hence $e$). For each coordinate $s_i$ it determines the binary digits of $s_i$ from the least significant upwards: the block entry $2^{w-1} s_i + e$ reveals the lowest bit by half-modulus rounding, and after subtracting the already known low bits from the entry $2^{w-1-t} s_i + e'$ the $t$-th bit is decoded in the same way.

## Proof sketch

Knowing the low $t$ bits $s'$ of $s_i$, the quantity $2^{w-1-t}(s_i - s') + e'$ equals $2^{w-1}\beta_t + e' \bmod q$ for the next bit $\beta_t$, so it decodes correctly whenever $4|e'| < q$. This is iterative nearest-plane decoding with respect to the short matrix $S_w$.

## Depends on

- [The binary gadget vector and gadget matrix](gadget-matrix.md)
- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)

## Proof depends on

- [The gadget lattice has a short basis-like matrix $S_w$](gadget-kernel-short-matrix.md)
- [Half-modulus encoding of a bit tolerates errors below $q/4$](half-modulus-bit-decoding.md)

## Sources

- Daniele Micciancio and Chris Peikert, "Trapdoors for Lattices: Simpler, Tighter, Faster, Smaller", Advances in Cryptology – EUROCRYPT 2012, 2012.
