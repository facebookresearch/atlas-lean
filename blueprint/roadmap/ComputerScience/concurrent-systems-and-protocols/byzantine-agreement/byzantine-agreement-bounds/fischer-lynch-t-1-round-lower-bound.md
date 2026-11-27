# Fischer–Lynch t + 1 round lower bound

For every $t \ge 0$, every $n \ge t + 2$, every nontrivial input set and every deterministic synchronous protocol with unrestricted messages and local computation, interactive consistency against $t$ Byzantine faults cannot be solved within $R \le t$ rounds. Likewise Boolean Byzantine agreement cannot be solved within $R \le t$ rounds for any $n \ge 2$. Together with the $n > 3t$ node bound, for $R \ge t + 1$ Boolean Byzantine agreement is solvable in $R$ rounds exactly when $n \le 1$ or $n > 3t$.

## Proof sketch

A chain argument: crash faulty processes one round earlier at a time, moving through a sequence of runs in which consecutive runs are indistinguishable to some correct process, from a run whose outputs are forced by validity to one whose outputs must differ; with only $t$ faults and $t$ rounds the chain cannot be broken.

## Depends on

- [Interactive consistency](interactive-consistency.md)
- [Reaching Byzantine agreement](../solves.md)

## Proof depends on

- [No synchronous protocol reaches Byzantine agreement when $3 \le n \le 3m$](../not-solves-of-card-le-three-mul.md)
- [Consensus with $f$ crash failures needs $f + 1$ rounds](../../synchronous-consensus-with-crash-failures/f-add-one-le-of-solves.md)
- [The oral messages algorithm solves the Byzantine generals problem](../../byzantine-generals-problem/byzantine-generals.md)

## Sources

- Michael J. Fischer and Nancy A. Lynch, "A Lower Bound for the Time to Assure Interactive Consistency", Information Processing Letters, 1982.
- Michael J. Fischer, Nancy A. Lynch and Michael Merritt, "Easy Impossibility Proofs for Distributed Consensus Problems", Proceedings of the Fourth Annual ACM Symposium on Principles of Distributed Computing, 1985.
- Leslie Lamport, Robert Shostak and Marshall Pease, "The Byzantine Generals Problem", ACM Transactions on Programming Languages and Systems, 1982.
