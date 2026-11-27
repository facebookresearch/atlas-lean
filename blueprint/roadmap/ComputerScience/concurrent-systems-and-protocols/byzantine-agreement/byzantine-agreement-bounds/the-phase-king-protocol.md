# The phase-king protocol

For $n > 4t$ processes and any decidable value set, the phase-king protocol runs $t + 1$ phases of two rounds each: in the first round of a phase all processes exchange their preferences and each computes the majority value $m$ among the received preferences and its multiplicity $c$; in the second round the phase's king broadcasts its own majority value, and each process keeps $m$ if $c > n/2 + t$ and otherwise adopts the king's value. It solves Byzantine agreement in $2(t + 1)$ rounds with every message a single value of $V$, so communication is polynomial. Moreover, Turpin and Coan's reduction converts any binary Byzantine agreement protocol into a multivalued one for $n > 3t$ at the cost of two extra rounds.

## Proof sketch

Some phase among $t + 1$ has a correct king, after which all correct processes hold the king's value; persistence shows a value with overwhelming support among correct processes survives every later phase. In Turpin–Coan, two exchange rounds determine a unique candidate value that correct processes can agree to adopt via the binary protocol.

## Depends on

- [Reaching Byzantine agreement](../solves.md)

## Proof depends on

- [No synchronous protocol reaches Byzantine agreement when $3 \le n \le 3m$](../not-solves-of-card-le-three-mul.md)

## Sources

- Piotr Berman and Juan A. Garay, "Asymptotically Optimal Distributed Consensus (Extended Abstract)", Automata, Languages and Programming (ICALP 1989), 1989.
- Piotr Berman, Juan A. Garay and Kenneth J. Perry, "Towards Optimal Distributed Consensus", 30th Annual Symposium on Foundations of Computer Science (FOCS 1989), 1989.
- Russell Turpin and Brian A. Coan, "Extending Binary Byzantine Agreement to Multivalued Byzantine Agreement", Information Processing Letters, 1984.
