# Explicit lossless vertex expanders yield linear-time decodable quantum LDPC codes

For every $\varepsilon, \beta \in (0, 1]$ there are $k = k(\varepsilon)$ and $d_0 = d_0(\varepsilon, \beta)$ such that for all $d_L, d_R \ge d_0$ with $\beta \le d_L/d_R \le \beta + \varepsilon$ there is an infinite family of $(k d_L, k d_R)$-biregular bipartite graphs $Z_n = (L_n, R_n, E_n)$ on $\Theta(n)$ vertices, output in time polynomial in $n$, that are two-sided $(1-\varepsilon)$-vertex expanders: for some $\eta > 0$, every $S \subseteq L_n$ with $|S| \le \eta |L_n|$ has at least $(1-\varepsilon) k d_L |S|$ neighbours in $R_n$, and every $T \subseteq R_n$ with $|T| \le \eta |R_n|$ has at least $(1-\varepsilon) k d_R |T|$ neighbours in $L_n$. Each $Z_n$ admits a free action of a group of size $O(|V(Z_n)|)$. Consequently, for every $r \in (0, 1)$ there are $\delta > 0$, $w \in \mathbb{N}$ and an explicit infinite family of quantum codes with parameters $[[n_i, k_i, d_i]]$ such that $k_i/n_i > r$, $d_i/n_i > \delta$, all stabilizers have weight $w$, and the family has a linear-time decoding algorithm.

## Proof sketch

The expander statement is Theorem 2.2 of the cited paper: the graphs are tripartite line products of a constant-size lossless gadget with bipartite graphs read off from Cayley cubical complexes over $\mathrm{PSL}(2, \mathbb{F}_q)$, whose strong local expansion makes small sets expand losslessly on both sides. The left action of $\mathrm{PSL}(2, \mathbb{F}_q)$ on the cubical complex is free and respects the gadget placement (Proposition A.3). Appendix A records the conditional code construction as Theorem A.2: two-sided lossless expanders of appropriately imbalanced degrees with a compatible free group action of linear size give a balanced-product family with the stated rate, distance, stabilizer weight and linear-time decoding; the graphs above satisfy its two hypotheses.

## Depends on

- [Quantum LDPC code families and asymptotically good quantum codes](../homological-quantum-ldpc-codes/quantum-ldpc-code-families-and-good-codes.md)

## Proof depends on

- [Balanced products of chain complexes over a group](../homological-quantum-ldpc-codes/balanced-product-of-chain-complexes.md)

## Sources

- Jun-Ting Hsieh, Alexander Lubotzky, Sidhanth Mohanty, Assaf Reiner, Rachel Yun Zhang, "Explicit lossless vertex expanders", FOCS (2025); arXiv:2504.15087.
