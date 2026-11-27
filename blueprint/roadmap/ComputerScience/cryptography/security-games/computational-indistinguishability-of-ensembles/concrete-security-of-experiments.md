# Concrete (resource-bounded) security of experiments

A security notion is *$(t, q, \varepsilon)$-secure* if every adversary running in time at most $t$ (in a fixed machine model) and making at most $q$ oracle queries of each kind has advantage at most $\varepsilon$ in the experiment. Reductions are stated concretely as $\mathrm{Adv}(A) \le f(\mathrm{Adv}(B_A))$ with $B_A$'s resources bounded in terms of $A$'s. Asymptotic security follows when $t$ and $q$ range over polynomials and $\varepsilon$ over negligible functions, but concrete statements keep the exact losses.

## Depends on

- [Distinguishing advantage](../games-and-advantages/advantage.md)
- [Asymptotic security](../asymptotic-security/asymptotically-secure.md)
- [Query bound](../oracle-algorithms/is-query-bounded.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- M. Bellare, A. Desai, E. Jokipii and P. Rogaway, "A Concrete Security Treatment of Symmetric Encryption", Proceedings of the 38th Annual IEEE Symposium on Foundations of Computer Science (FOCS), 1997.
