# Shared multiplication from 1-out-of-4 oblivious transfer

In the two-party *shared multiplication* functionality, party $1$ holds bits $(a_1, b_1)$, party $2$ holds $(a_2, b_2)$, and they receive uniform additive shares $c_1 \oplus c_2 = (a_1 \oplus a_2)(b_1 \oplus b_2)$. In the $\mathrm{OT}^4_1$-hybrid protocol, party $1$ draws a uniform bit $c_1$ and offers the table $t_{(a,b)} = c_1 \oplus (a_1 \oplus a)(b_1 \oplus b)$ for $(a, b) \in \{0,1\}^2$, and party $2$ selects index $(a_2, b_2)$ and outputs $c_2 = t_{(a_2, b_2)}$. The protocol is correct and perfectly semi-honest private in the $\mathrm{OT}^4_1$-hybrid model against every static coalition. The $m$-party shared multiplication of $\bigl(\sum_i a_i\bigr)\bigl(\sum_i b_i\bigr)$ reduces to $m(m-1)$ pairwise two-party invocations plus local products $a_i b_i$, again perfectly privately.

## Proof sketch

Party $1$'s view is its own coins; party $2$'s view is the selected table entry, which is its output. For $m$ parties expand $\sum_{i,j} a_i b_j$ and compute every cross term $a_i b_j + a_j b_i$ with two pairwise invocations.

## Depends on

- [Synchronous oracle-aided multiparty protocols and perfect semi-honest privacy](oracle-aided-protocols-and-perfect-privacy.md)
- [Ideal 1-out-of-2, batched and 1-out-of-4 oblivious transfer](../oblivious-transfer-protocols/oblivious-transfer-functionalities.md)

## Sources

- Oded Goldreich, "Foundations of Cryptography, Volume 2: Basic Applications", Cambridge University Press, 2004.
