# MPC(eps) model

In the massively parallel communication (MPC) model with $p \ge 1$ servers and space exponent
$0 \le \varepsilon \le 1$, an input of $M$ bits is initially distributed evenly among the servers. In the variant with input
servers, each input relation is instead held by its own input server, which sends messages to the
servers only in the first round; lower bounds proved for that variant also hold for the standard one. Computation
proceeds in rounds; in each round every server performs local computation and then sends messages to
other servers over private channels, and the load of a round is the maximum number of bits received by a
server in it. An algorithm has load $L$ if every round has load at most $L$, and the model of the cited
source requires $L \le c\, M / p^{1-\varepsilon}$ for a constant $c$ independent of $M$ and $p$. Algorithms may use shared randomness and must produce the
correct output with probability at least $1 - \eta$ for a stated failure probability $\eta$; the output is
the union of the servers' outputs.

## Sources

- Communication Steps for Parallel Query Processing (Beame, Koutris, Suciu, PODS 2013) — Beame, Koutris, Suciu; ACM PODS, authors' copy, Sections 2.1, 2.2 and 2.4. <https://homes.cs.washington.edu/~beame/papers/mpcpods.pdf>
