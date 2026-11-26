# Prefix-free encoding of messages

A *prefix-free encoding* is an injective map $\mathrm{pf} : M \to X^{\le \ell}$ into block sequences such that no image is a proper prefix of another. Examples: prepending the block count, or appending an end-marker block that no message block can equal. A *randomized $\varepsilon$-prefix-free encoding* is a keyed map $\mathrm{rpf} : K \times M \to X^{\le \ell}$ such that for all $m_0 \ne m_1$ in $M$, the probability over a uniform key $k$ that one of $\mathrm{rpf}(k, m_0)$ and $\mathrm{rpf}(k, m_1)$ is a prefix of the other is at most $\varepsilon$; the image of $\mathrm{rpf}(k, \cdot)$ need not be a prefix-free set, and $\mathrm{rpf}(k, \cdot)$ need not be injective (Boneh and Shoup, Definition 6.6).

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
