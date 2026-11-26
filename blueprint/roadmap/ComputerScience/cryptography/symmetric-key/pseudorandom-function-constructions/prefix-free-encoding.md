# Prefix-free encoding of messages

A *prefix-free encoding* is an injective map $\mathrm{pf} : M \to X^{\le \ell}$ into block sequences such that no image is a proper prefix of another. Examples: prepending the block count, or appending an end-marker block. A *randomized* prefix-free encoding is a keyed family whose images form a prefix-free set except with negligible probability over the key.

## Depends on

- [Prefix-free pseudorandom function](prefix-free-pseudorandom-function.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
