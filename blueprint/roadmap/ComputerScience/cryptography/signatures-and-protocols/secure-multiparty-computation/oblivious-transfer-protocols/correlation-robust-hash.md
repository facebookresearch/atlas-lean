# Correlation-robust hash functions

A hash family $H : [m] \times \{0,1\}^\kappa \to \{0,1\}^\ell$ is *correlation robust* if for a uniformly random secret $s \in \{0,1\}^\kappa$ and uniformly random $t_1, \dots, t_m \in \{0,1\}^\kappa$ (or any $t_j$ chosen independently of $s$), the tuple

$$
\bigl(t_1, \dots, t_m,\; H(1, t_1 \oplus s), \dots, H(m, t_m \oplus s)\bigr)
$$

is computationally indistinguishable from $(t_1, \dots, t_m, U_1, \dots, U_m)$ with independent uniform $U_j$. A random oracle is correlation robust with advantage at most $q\, m/2^\kappa$ for an adversary making $q$ oracle queries, since distinguishing requires querying some $t_j \oplus s$. Correlation robustness is the assumption under which IKNP oblivious-transfer extension is secure against the receiver.

## Depends on

- [The random oracle model](../../../public-key/random-oracle-constructions/the-random-oracle-model.md)
- [Distinguishing advantage](../../../security-games/games-and-advantages/advantage.md)

## Sources

- Yuval Ishai, Joe Kilian, Kobbi Nissim and Erez Petrank, "Extending Oblivious Transfers Efficiently", Advances in Cryptology – CRYPTO 2003, 2003.
