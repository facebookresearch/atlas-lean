# An ignored ciphertext bit breaks CCA security

Let $(G, E, D)$ be a CCA-secure public-key scheme and define $E'(pk, m) = E(pk, m) \| 0$ with $D'(sk, c\|b) = D(sk, c)$, ignoring the last bit. Then $E'$ is not CCA secure: flipping the last bit of the challenge gives a different ciphertext that decrypts to $m_b$. The weakness is only this ciphertext slack: $E'$ still satisfies the relaxed, replayable notion of chosen-ciphertext security (RCCA).

## Proof sketch

The CCA adversary queries $c^* \oplus 0\cdots01$, which differs from $c^*$, and its decryption is $m_b$.

## Depends on

- [1CCA security of public-key encryption](one-cca-security.md)

## Sources

- R. Canetti, H. Krawczyk and J. B. Nielsen, "Relaxing Chosen-Ciphertext Security", Advances in Cryptology – CRYPTO 2003, LNCS 2729, Springer, 2003, pp. 565–582.
