# Deterministic symmetric ciphers are not CPA secure

Let a symmetric cipher on $n$-bit messages encrypt $0^n$ deterministically under every key (from some $n_0$ on). The adversary that makes the queries $(0^n, 1^n)$ and then $(0^n, 0^n)$ and outputs $0$ iff the two answers are equal has CPA advantage $1$. Likewise a cipher with zero ciphertext expansion (ciphertexts no longer than messages) is not CPA secure.

## Proof sketch

Under bit $0$ both queries encrypt $0^n$ and give the same ciphertext. Under bit $1$ the first query encrypts $1^n$, which by correctness cannot share a ciphertext with $0^n$. A zero-expansion cipher is a permutation for each key and hence deterministic.

## Depends on

- [CPA indistinguishability experiment](../../security-games/generic-security-games/cpa-game.md)
- [Correctness of a private-key encryption scheme](../../security-games/generic-security-games/correct.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", 3rd edition, CRC Press, 2020.
