# The Piano preprocessing PIR scheme

Split $[n]$ into $\sqrt n$ chunks of size $\sqrt n$. In *Piano*, a primary hint is a set $S$ containing one pseudorandomly chosen offset in every chunk together with the parity of the database on $S$; backup hints are sets with one chunk punctured, with their parities. To query $x$ in chunk $c$, the client finds a primary hint $S$ containing $x$, replaces the element of $S$ in chunk $c$ by a fresh random offset $r$, and sends this edited set $S'$; the server returns, for every chunk $j$, the parity of $S'$ with its chunk-$j$ element removed, and the client XORs the answer for $j = c$, which is the parity of $S \setminus \{x\}$, with the hint parity to obtain $x_x$ (the *online reconstruction identity*); it then refreshes the consumed primary hint from a backup hint for chunk $c$, whose punctured parity XOR $x_x$ is the full parity of the new set (the *refresh identity*). With $\tilde O(\sqrt n)$ hints, the client storage and the server's online work are $\tilde O(\sqrt n)$, every query is answered correctly except with negligible probability, and the server's view of every adaptive sequence of queries is a sequence of uniformly random sets with one element per chunk, independent of the queries.

## Proof sketch

The reconstruction and refresh identities are parity computations. Privacy follows from the state-invariance criterion: after a query, the replaced hint has the law of a fresh primary hint conditioned on the history, so every edited set is uniform among sets with one element per chunk.

## Depends on

- [Client-preprocessing single-server PIR](client-preprocessing-pir.md)

## Sources

- Mingxun Zhou, Andrew Park, Wenting Zheng and Elaine Shi, "Piano: Extremely Simple, Single-Server PIR with Sublinear Server Computation", 2024 IEEE Symposium on Security and Privacy (SP), 2024.
