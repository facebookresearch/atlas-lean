# Beaver's multiplication with dealer triples is correct and perfectly private

Work over $\mathbb{Z}_p$ with $m \ge 1$ parties holding additive shares $[x], [y]$. A trusted dealer gives party $i$ a share $(a_i, b_i, c_i)$ of a uniform *Beaver triple* with $\sum_i c_i = (\sum_i a_i)(\sum_i b_i)$; every proper coalition's triple shares are uniform. To multiply, the parties open $d = x - a$ and $e = y - b$ and party $i$ sets $z_i = c_i + d\, b_i + e\, a_i$, with one designated party adding $de$. Then $\sum_i z_i = xy$, and for every proper static coalition the joint distribution of the corrupted views and all outputs is exactly simulatable from the coalition's inputs and outputs (the opened $d, e$ are uniform one-time-pad encryptions). The protocol is not secure against active deviation: a party that adds $\delta$ to its opening of $d$ shifts the product by $\delta \cdot y$.

## Proof sketch

$\sum_i z_i = ab + (x-a)b + (y-b)a + (x-a)(y-b) = xy$. Since $a$ and $b$ are uniform and hidden from any proper coalition, $d$ and $e$ are uniform and independent of $x, y$, and the remaining shares are uniform subject to summing to the outputs.

## Depends on

- [Synchronous oracle-aided multiparty protocols and perfect semi-honest privacy](../semi-honest-mpc-foundations/oracle-aided-protocols-and-perfect-privacy.md)

## Sources

- Donald Beaver, "Efficient Multiparty Protocols Using Circuit Randomization", Advances in Cryptology –- CRYPTO '91, 1992.
- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
