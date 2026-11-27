# Correctness of ML-DSA

Let $c$ have exactly $\tau$ nonzero coefficients in $\{\pm 1\}$ and $\|\mathbf{s}\|_\infty \le \eta$; then $\|c\,\mathbf{s}\|_\infty \le \tau\eta = \beta$. Consequently every signature output by an ML-DSA signing attempt that passes all rejection checks verifies under the matching public key: from $\|\mathrm{LowBits}(\mathbf{A}\mathbf{y} - c\mathbf{s}_2)\|_\infty < \gamma_2 - \beta$ one gets $\mathrm{HighBits}(\mathbf{A}\mathbf{z} - c\mathbf{t}) = \mathrm{HighBits}(\mathbf{A}\mathbf{y}) = \mathbf{w}_1$, and the check $\|c\mathbf{t}_0\|_\infty < \gamma_2$ makes the hint recover $\mathbf{w}_1$ from $\mathbf{A}\mathbf{z} - c\mathbf{t}_1 2^d$. This holds for every mask sampler and every number of retries: the output signature is computed by a single attempt that passed all checks, and the argument concerns that attempt alone.

## Proof sketch

$\mathbf{A}\mathbf{z} - c\mathbf{t} = \mathbf{A}\mathbf{y} - c\mathbf{s}_2$, and adding a vector of norm at most $\beta$ to a point whose low bits are below $\gamma_2 - \beta$ preserves the high bits. Then apply the hint property to $\mathbf{A}\mathbf{z} - c\mathbf{t}_1 2^d = (\mathbf{A}\mathbf{z} - c\mathbf{t}) + c\mathbf{t}_0$. Earlier aborted attempts do not enter the output, and verification reads only the output $(\tilde c, \mathbf{z}, \mathbf{h})$, the public key and the message, so neither the mask sampler nor the number of retries plays a role.

## Depends on

- [The ML-DSA signature scheme](ml-dsa-scheme.md)
- [Correctness of a signature scheme](../../../security-games/generic-security-games/correct-4.md)

## Proof depends on

- [Reconstruction and uniqueness of the ML-DSA decompositions](ml-dsa-decomposition-properties.md)
- [MakeHint and UseHint](ml-dsa-hints.md)

## Sources

- Léo Ducas et al., "CRYSTALS-Dilithium: A Lattice-Based Digital Signature Scheme", IACR Transactions on Cryptographic Hardware and Embedded Systems, 2018.
- National Institute of Standards and Technology, "Module-Lattice-Based Digital Signature Standard", National Institute of Standards and Technology, 2024.
