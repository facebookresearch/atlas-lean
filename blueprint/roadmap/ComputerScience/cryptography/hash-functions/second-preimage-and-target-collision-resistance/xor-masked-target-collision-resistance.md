# Masking the input with the key turns second-preimage resistance into target collision resistance

Let $H$ be a second-preimage-resistant function on $n$-bit inputs. The keyed family $H_{\mathrm{tcr}}(k, m) = H(k \oplus m)$ with uniform $n$-bit keys is target collision resistant on $n$-bit messages.

## Proof sketch

Given a challenge $x$ for second preimages, the reduction runs the TCR adversary's first stage to get its target $m_0$, sets the key $k = x \oplus m_0$ (uniform since $x$ is), and maps a collision $m_1$ to the second preimage $k \oplus m_1$.

## Depends on

- [Second-preimage resistance](second-preimage-resistance.md)
- [Collision resistance and target collision resistance](../collision-resistance-and-target-collision-resistance.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
