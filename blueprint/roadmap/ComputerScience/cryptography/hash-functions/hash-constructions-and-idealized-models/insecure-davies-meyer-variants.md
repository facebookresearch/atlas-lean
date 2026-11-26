# Insecure Davies–Meyer variants admit two-query collision finders

Let keys and blocks share a group $X$. For $h_4(k, x) = E(k, x) + k$ and $h_5(k, x) = E(k, k + x) + k$, for any two keys $k_1 \ne k_2$ and target $y$, the inputs $(k_i, E^{-1}(k_i, y - k_i))$ (respectively $(k_i, E^{-1}(k_i, y - k_i) - k_i)$) are distinct and both map to $y$. Hence in the ideal cipher model a finder making two inverse queries always succeeds, and for any concrete cipher these give explicit collisions.

## Proof sketch

Substitute the inverse into the definition: $E(k_i, E^{-1}(k_i, y - k_i)) + k_i = y$. Distinct keys give distinct inputs.

## Depends on

- [Davies–Meyer compression function](davies-meyer-compression.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- J. Black, P. Rogaway and T. Shrimpton, "Black-Box Analysis of the Block-Cipher-Based Hash-Function Constructions from PGV", Advances in Cryptology (CRYPTO 2002), LNCS 2442, 2002.
