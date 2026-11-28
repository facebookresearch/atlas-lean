# Correlation-robust and circular correlation-robust hash families

A hash family $H$ is *correlation robust* (Ishai, Kilian, Nissim and Petrank; Choi, Katz, Kumaresan and Zhou, Definition 1) if for a uniform secret $\Delta \in \{0,1\}^n$, independent uniform inputs $w_1, \dots, w_p$ ($p$ polynomial in $n$) and every non-uniform polynomial-time distinguisher, the tuple $(w_1, \dots, w_p, H(w_1 \oplus \Delta), \dots, H(w_p \oplus \Delta))$ is indistinguishable from $(w_1, \dots, w_p, u_1, \dots, u_p)$ with independent uniform $u_i$; the inputs are random and given to the distinguisher, not chosen by it. *Circular* correlation robustness (Choi et al., Definition 4) is an adaptive oracle notion for a hash taking two keys and a tweak $g$: no non-uniform polynomial-time distinguisher can tell apart, with non-negligible advantage, the oracle that answers a query $(w, w', g, b_1, b_2, b_3)$ with bits $b_1, b_2, b_3$ by $H(w \oplus b_1\Delta \,\|\, w' \oplus b_2\Delta \,\|\, g) \oplus b_3\Delta$ from an oracle that answers each new query with a fresh uniform string (and repeats its answer on a repeated query), provided its queries are *legal*: it never queries with $b_1 = b_2 = 0$ (it can evaluate $H$ itself there), and never queries both $(w, w', g, b_1, b_2, 0)$ and $(w, w', g, b_1, b_2, 1)$, since XORing the two answers would reveal $\Delta$. Without these restrictions the notion is unsatisfiable. Circular correlation robustness suffices to prove the free-XOR technique for garbled circuits secure against semi-honest adversaries (Choi et al., Theorem 3).

## Remarks

Choi et al. also rule out a fully black-box proof of that security from the non-circular adaptive variant (their Definition 3 and Section 3).

## Depends on

- [PRF advantage](../../symmetric-key/pseudorandom-functions/prf-advantage.md)
- [Free-XOR garbling](../../signatures-and-protocols/secure-multiparty-computation/boolean-garbling-constructions/free-xor-garbling.md)
- [Ideal 1-out-of-2, batched and 1-out-of-4 oblivious transfer](../../signatures-and-protocols/secure-multiparty-computation/oblivious-transfer-protocols/oblivious-transfer-functionalities.md)
- [Negligible advantage](../../security-games/asymptotic-security/negligible-adv.md)
## Sources

- Y. Ishai, J. Kilian, K. Nissim and E. Petrank, "Extending Oblivious Transfers Efficiently", Advances in Cryptology (CRYPTO 2003), LNCS 2729, 2003.
- S. G. Choi, J. Katz, R. Kumaresan and H.-S. Zhou, "On the Security of the Free-XOR Technique", Theory of Cryptography (TCC 2012), LNCS 7194, 2012, Definitions 1, 3 and 4, Theorem 3.
