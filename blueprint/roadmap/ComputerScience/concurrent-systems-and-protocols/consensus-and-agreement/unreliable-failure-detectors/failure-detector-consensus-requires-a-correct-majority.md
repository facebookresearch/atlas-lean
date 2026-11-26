# Failure-detector consensus requires a correct majority

In the asynchronous round model augmented with a failure detector, no protocol solves consensus with uniform agreement and validity tolerating $t$ crashes when $2 \le n \le 2t$, even with an eventually perfect failure detector. For $n > 2t$, the rotating-coordinator protocol with $\Diamond\mathcal S$ (or $\Diamond \mathcal W$) is safe in every run and terminates.

## Proof sketch

With $n \le 2t$, split processes into two halves; an eventually perfect detector may wrongly suspect the other half for an arbitrarily long finite time, during which each half must decide alone, as if the other had crashed, so the halves can decide differently.

## Depends on

- [Failure detector classes](../failure-detector-classes.md)
- [Resilient consensus protocols](../resilient-consensus-protocols.md)

## Proof depends on

- [Safety of rotating-coordinator consensus](../safety-of-rotating-coordinator-consensus.md)
- [Termination of rotating-coordinator consensus with an eventually strong detector](../termination-of-rotating-coordinator-consensus.md)
- [Consensus under partial synchrony needs a majority](../consensus-under-partial-synchrony-needs-a.md)

## Sources

- Tushar Deepak Chandra and Sam Toueg, "Unreliable Failure Detectors for Reliable Distributed Systems", Journal of the ACM, 1996.
- Tushar Deepak Chandra, Vassos Hadzilacos and Sam Toueg, "The Weakest Failure Detector for Solving Consensus", Journal of the ACM, 1996.
