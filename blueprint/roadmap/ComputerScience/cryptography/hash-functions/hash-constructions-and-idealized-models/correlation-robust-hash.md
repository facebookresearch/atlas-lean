# Correlation-robust and circular correlation-robust hash families

A hash family $H$ is *correlation robust* if for a uniform secret $\Delta \in \{0,1\}^n$, the values $H(x_1 \oplus \Delta), \dots, H(x_q \oplus \Delta)$ on adversarially chosen distinct inputs are indistinguishable from uniform. It is *circular correlation robust* if additionally the adversary may query $H(x \oplus \Delta) \oplus b\,\Delta$ for chosen bits $b$; this is the property used to prove the free-XOR technique for garbled circuits secure.

## Depends on

- [PRF advantage](../../symmetric-key/pseudorandom-functions/prf-advantage.md)

## Sources

- Y. Ishai, J. Kilian, K. Nissim and E. Petrank, "Extending Oblivious Transfers Efficiently", Advances in Cryptology (CRYPTO 2003), LNCS 2729, 2003.
- S. G. Choi, J. Katz, R. Kumaresan and H.-S. Zhou, "On the Security of the Free-XOR Technique", Theory of Cryptography (TCC 2012), LNCS 7194, 2012.
