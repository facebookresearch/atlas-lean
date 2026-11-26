# Explicit lossless vertex expanders yield linear-time decodable quantum LDPC codes

For every $\varepsilon > 0$ and sufficiently large $d$, there are $\gamma=\gamma(\varepsilon,d)>0$ and explicit $d$-regular graphs in which every vertex set $S$ of size at most $\gamma |V|$ has at least $(1 - \varepsilon) d |S|$ neighbours (hence at least $(1 - 2\varepsilon) d |S|$ unique neighbours), admitting a free group action. Plugged into the Lin-Hsieh construction, which requires two-sided lossless expansion with a free group action, they give explicit quantum LDPC codes of constant rate and linear distance with a linear-time decoder.

## Proof sketch

Hsieh, Lubotzky, Mohanty, Reiner and Zhang take an appropriate product of a constant-size lossless expander gadget with a base graph derived from Ramanujan Cayley cubical complexes; the cubical structure provides strong local expansion of links, so small sets expand losslessly. The resulting graph inherits the free action of the underlying group, as required by the balanced-product construction of Lin and Hsieh, whose small-set-flip decoder works under lossless expansion.

## Depends on

- [Quantum LDPC code families and asymptotically good quantum codes](../homological-quantum-ldpc-codes/quantum-ldpc-code-families-and-good-codes.md)

## Proof depends on

- [Balanced products of chain complexes over a group](../homological-quantum-ldpc-codes/balanced-product-of-chain-complexes.md)
- [Sipser-Spielman expander codes](../../../InformationTheory/error-correcting-codes/sipser-spielman-expander-codes.md)
- [Expander code distance](../../../InformationTheory/error-correcting-codes/expander-code-distance.md)

## Sources

- Jun-Ting Hsieh, Alexander Lubotzky, Sidhanth Mohanty, Assaf Reiner, Rachel Yun Zhang, "Explicit lossless vertex expanders", FOCS (2025); arXiv:2504.15087.
- Ting-Chun Lin, Min-Hsiu Hsieh, "Good quantum LDPC codes with linear time decoder from lossless expanders", arXiv:2203.03581 (2022).
