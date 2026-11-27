# Linear cryptanalysis: majority vote recovers a key parity bit

Let $E : \{0,1\}^h \times \{0,1\}^n \to \{0,1\}^n$, masks $S_0, S_1 \subseteq [n]$, $S_2 \subseteq [h]$ and $\varepsilon \ge 0$ satisfy the linear relation: for every key $k$, $m[S_0] \oplus E(k,m)[S_1] = k[S_2]$ for at least a $\tfrac12 + \varepsilon$ fraction of messages $m$, where $z[S] = \bigoplus_{i \in S} z_i$. For independent uniform known plaintexts $m_1, \dots, m_t$, the majority of the bits $m_i[S_0] \oplus E(k, m_i)[S_1]$ equals $k[S_2]$ with probability at least

$$1 - e^{-2t\varepsilon^2}.$$

## Proof sketch

Each bit independently equals $k[S_2]$ with probability at least $\tfrac12 + \varepsilon$; Hoeffding's inequality bounds the probability that at most half of them do.

## Depends on

- [Block cipher (uniform family)](block-cipher.md)

## Proof depends on

- [Hoeffding lower-tail bound for Bernoulli sums](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/hoeffding-binomial-lower-tail.md)

## Sources

- M. Matsui, "Linear Cryptanalysis Method for DES Cipher", Advances in Cryptology (EUROCRYPT 1993), LNCS 765, 1994.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
