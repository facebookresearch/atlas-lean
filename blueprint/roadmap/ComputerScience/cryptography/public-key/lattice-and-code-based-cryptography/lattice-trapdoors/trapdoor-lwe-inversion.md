# LWE inversion with a $G$-trapdoor

Let $R$ be a $G$-trapdoor with invertible tag $H$ for $A \in \mathbb{Z}_q^{\ell \times (\bar m + \ell w)}$, $q = 2^w$. There is a deterministic polynomial-time algorithm that, given $R$, $H$ and $b^{\mathsf T} = s^{\mathsf T} A + e^{\mathsf T} \bmod q$ with an integer error $e$ such that $4\,\bigl|\bigl(e^{\mathsf T}\binom{R}{I}\bigr)_j\bigr| < q$ for all $j$, recovers $s$ and $e$. It computes $b^{\mathsf T}\binom{R}{I} = (H^{\mathsf T} s)^{\mathsf T} G + e^{\mathsf T}\binom{R}{I}$, inverts the gadget LWE instance to obtain $H^{\mathsf T}s$, and multiplies by $(H^{\mathsf T})^{-1}$. In particular, if $|e_i| \le \alpha$ for all $i$ and every column of $\binom{R}{I}$ has $\ell_1$ norm at most $L$, inversion succeeds when $4 \alpha L < q$.

## Proof sketch

Multiplying by the trapdoor transform turns an LWE sample for $A$ into a gadget LWE sample with error $e^{\mathsf T}\binom{R}{I}$, whose coordinates are bounded by $\alpha L$; then apply gadget inversion.

## Depends on

- [Micciancio–Peikert $G$-trapdoors and tagged parity-check matrices](micciancio-peikert-trapdoor.md)
- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)

## Proof depends on

- [Efficient inversion of gadget LWE](gadget-lwe-inversion.md)
- [Algebraic properties of Micciancio–Peikert trapdoors](trapdoor-kernel-lifting.md)

## Sources

- Daniele Micciancio and Chris Peikert, "Trapdoors for Lattices: Simpler, Tighter, Faster, Smaller", Advances in Cryptology – EUROCRYPT 2012, 2012.
