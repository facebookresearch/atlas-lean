# Synchronous oracle-aided multiparty protocols and perfect semi-honest privacy

An *$m$-party synchronous protocol* proceeds in rounds over pairwise private authenticated channels; in each round every party either sends messages computed from its view or the parties jointly call a $k$-ary *ideal oracle* (a functionality) on inputs supplied by designated parties, each receiving its own slot of the answer. The *view* of party $i$ consists of its input $x_i$, its private coins $r_i$, the messages addressed to $i$ and the oracle answers for slots assigned to $i$; its output is a deterministic function of its view. For a (possibly randomized) functionality $f$ and a coalition $I \subseteq [m]$, the *real joint distribution* is $(\{V_i\}_{i \in I}, (y_1, \dots, y_m))$ from an honest execution, and the *ideal joint distribution* with a coalition simulator $\mathcal{S}$ is $(\mathcal{S}(I, \{x_i, y_i\}_{i \in I}), (y_1, \dots, y_m))$ with $(y_i) \leftarrow f(x)$. The protocol is *perfectly semi-honest private* (against all coalitions, all proper coalitions, or all coalitions of size at most $t$) if for each such $I$ some simulator makes the two joint distributions equal for every input. Perfect privacy is equivalent to every distinguisher having advantage zero between the two distributions.

## Depends on

- [Multiparty security against semi-honest adversaries](../multiparty-security-against-semi-honest.md)
- [Distinguishing advantage](../../../security-games/games-and-advantages/advantage.md)

## Sources

- Oded Goldreich, "Foundations of Cryptography, Volume 2: Basic Applications", Cambridge University Press, 2004.
