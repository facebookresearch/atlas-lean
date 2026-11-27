# The Piano preprocessing PIR scheme

Split $[n]$ into $\sqrt n$ chunks of size $\sqrt n$. In *Piano*, in one streaming pass over the database the client stores primary hints, each a set $S$ containing one pseudorandomly chosen offset in every chunk (given by a PRF key) together with the parity $p$ of the database on $S$; for every chunk, backup hints, which are such sets with that chunk punctured, with their parities; and for every chunk, replacement entries $(r, \mathrm{DB}[r])$ for uniformly random indices $r$ of the chunk. To query $x$ in chunk $j^*$, the client finds a primary hint $(S, p)$ with $x \in S$, takes the next unused replacement entry $(r, \mathrm{DB}[r])$ of chunk $j^*$, and sends $S' = S\langle j^* \to r\rangle$, the set $S$ with its chunk-$j^*$ element replaced by $r$; the server returns the single parity $q$ of the database on $S'$, and the client outputs $q \oplus p \oplus \mathrm{DB}[r] = \mathrm{DB}[x]$, since $q$ is the parity of $S \setminus \{x\}$ XOR $\mathrm{DB}[r]$ (the *online reconstruction identity*). It then replaces the consumed primary hint by the next backup hint of chunk $j^*$, with set $T$ and parity $p_T$, completed with $x$: the new primary hint is $T\langle j^* \to x\rangle$ with parity $p_T \oplus \mathrm{DB}[x]$ (the *refresh identity*). With $\tilde O(\sqrt n)$ hints and replacement entries this serves $Q = \tilde O(\sqrt n)$ distinct queries; a public pseudorandom permutation of the indices, local caching of recent answers and re-running the preprocessing for each window of $Q$ queries extend it to unbounded adaptive queries. The client storage and the amortized communication and server work per query are $\tilde O(\sqrt n)$, every query is answered correctly except with negligible probability, and the server's view of every adaptive sequence of queries is computationally indistinguishable from a sequence of independent uniformly random sets with one element per chunk, which does not depend on the queries.

## Proof sketch

The reconstruction and refresh identities are parity computations. For privacy, replace the PRF by a truly random function (PRF security). Then each primary hint is a uniform set with one element per chunk; the hint used for $x$ is uniform subject to containing $x$, so the edited set $S'$ is uniform among sets with one element per chunk, and the refreshed hint is again uniform subject to containing $x$, so the law of the primary table given the history is unchanged.

## Depends on

- [Client-preprocessing single-server PIR](client-preprocessing-pir.md)
- [PRF advantage](../../../symmetric-key/pseudorandom-functions/prf-advantage.md)
- [PRP advantage](../../../symmetric-key/pseudorandom-permutations/prp-advantage.md)

## Sources

- Mingxun Zhou, Andrew Park, Wenting Zheng and Elaine Shi, "Piano: Extremely Simple, Single-Server PIR with Sublinear Server Computation", 2024 IEEE Symposium on Security and Privacy (SP), 2024.
