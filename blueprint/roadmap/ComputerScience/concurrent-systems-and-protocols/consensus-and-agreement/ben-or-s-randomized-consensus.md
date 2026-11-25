# Ben-Or's randomized consensus

Consider binary consensus among $n$ asynchronous message-passing processes of which at most $f < n/2$ may crash, with reliable delivery of messages between nonfaulty processes, independent fair coins, an adversarial scheduler that does not see coin flips before they occur, and fair activation: every nonfaulty process takes infinitely many steps. Ben-Or's protocol, which proceeds in rounds of a report phase and a proposal phase and decides a value proposed by more than $f$ processes, flipping a coin when no value is proposed by enough processes, satisfies agreement and validity in every execution, and every nonfaulty process decides with probability $1$.

## Depends on

- [FLP impossibility of asynchronous consensus with agreement, validity and termination](../flp-impossibility/flp-impossibility.md)
- [An admissible pattern has at most $T$ faulty processes](../synchronous-consensus-with-crash-failures/card-faulty-le.md)
- [Weak and strong fairness](../distributed-execution-models/weak-and-strong-fairness.md)

## Expansion

This page becomes ready once:

- Channel semantics variants (statement prerequisite; not yet stated)

## Sources

- M. Ben-Or, "Another advantage of free choice: completely asynchronous agreement protocols", *Proceedings of the 2nd ACM PODC*, 1983
- J. Aspnes, *Notes on Theory of Distributed Systems*, Yale University, 2020, <https://arxiv.org/abs/2001.04235>
