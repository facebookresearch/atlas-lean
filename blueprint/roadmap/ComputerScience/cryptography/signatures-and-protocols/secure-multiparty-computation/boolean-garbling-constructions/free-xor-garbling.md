# Free-XOR garbling

*Free-XOR* garbling fixes one secret global offset $\Delta \in L$ of colour $1$ for the whole circuit (with $L$ of characteristic two, e.g. $\{0,1\}^k$): the two labels of every wire $i$ are $W_i$ and $W_i \oplus \Delta$, the second encoding the bit $1$. An XOR gate with inputs $a, b$ needs no garbled table: its output zero-label is $W_c = W_a \oplus W_b$, and the evaluator XORs the labels it holds. Non-XOR gates are garbled with four rows (or three with row reduction) using a tweakable hash $H$ with a distinct tweak for each row.

## Depends on

- [Point-and-permute garbling](point-and-permute-garbling.md)
- [Circular correlation robust hash functions](../garbling-scheme-security/circular-correlation-robustness.md)

## Sources

- Vladimir Kolesnikov and Thomas Schneider, "Improved Garbled Circuit: Free XOR Gates and Applications", Automata, Languages and Programming, 35th International Colloquium, 2008.
- Seung Geol Choi, Jonathan Katz, Ranjit Kumaresan and Hong-Sheng Zhou, "On the Security of the ``Free-XOR'' Technique", Theory of Cryptography, 2012.
