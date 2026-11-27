# Semantic security implies security against parity prediction

Let a cipher with message space $\{0,1\}^{L}$, where $L \ge 1$, be one-time semantically secure. Then every efficient adversary, given the encryption of a uniform message $m$, predicts the parity $\bigoplus_i m_i$ with probability at most $\tfrac12 + \mathrm{SSadv}$ for a comparable semantic-security adversary.

## Proof sketch

Submit a uniform message of parity $0$ and a uniform message of parity $1$ and output the predicted parity; the two challenge distributions together form a uniform message whose parity is the challenge bit.

## Depends on

- [Semantic security with error $\varepsilon$](../../security-games/semantic-security-and-indistinguishability/semantically-secure.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
