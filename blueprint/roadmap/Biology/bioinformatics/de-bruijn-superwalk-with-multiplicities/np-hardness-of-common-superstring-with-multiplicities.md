# NP-hardness of common superstring with multiplicities

For a string $S$ over an alphabet $\Sigma$ and $c \in \Sigma$, let $L_c(S)$ be the number of occurrences of $c$ in $S$. The **Common Superstring with Multiplicities** (CSM) problem asks, given strings $S_1, \dots, S_n$ and nonnegative integers $l_c$ ($c \in \Sigma$, encoded in unary), whether there is a string $S$ such that every $S_i$ is a substring of $S$ and $L_c(S) = l_c$ for every $c \in \Sigma$.

**Theorem.** CSM is NP-hard already for $|\Sigma| = 2$ (Kapun and Tsarev 2013, Theorem 1).

## Expansion

Reduce binary Shortest Common Superstring (does $S'_1, \dots, S'_n$ have a superstring of length at most $l'$?). Encode each bit by a block, $T_0 = 000111$ and $T_1 = 001011$: both have three zeros and three ones, and no proper suffix of either equals a proper prefix of either. Map $S'_k \mapsto S_k = T(S'_k)$ (blockwise) and set $l_0 = l_1 = 3l'$. A superstring of length $l'' \le l'$ pads to $S'0^{l'-l''}$ whose encoding solves CSM. Conversely, the non-overlap property forces every occurrence of an encoded string inside a covering superstring to start at a position $\equiv 1 \pmod 6$, so any shortest CSM superstring decodes to a binary superstring of length at most $l'$ (Lemmas 4–7).

## Sources

- E. Kapun and F. Tsarev, *De Bruijn superwalk with multiplicities problem is NP-hard*, BMC Bioinformatics 14 (Suppl 5) (2013), S7, Theorem 1 and Lemmas 1–7. <https://doi.org/10.1186/1471-2105-14-S5-S7> (PMCID: PMC3622630)
