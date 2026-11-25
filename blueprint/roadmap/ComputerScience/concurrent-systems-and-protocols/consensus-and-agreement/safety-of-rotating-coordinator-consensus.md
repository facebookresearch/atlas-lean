# Safety of rotating-coordinator consensus

Consider Chandra and Toueg's rotating-coordinator consensus algorithm for $n$ processes in an asynchronous system with reliable channels, in which fewer than $\lceil n/2 \rceil$ processes crash and processes communicate by reliable broadcast. In every run of the algorithm with a failure detector of class $\Diamond\mathcal{S}$ in which all correct processes propose a value:

- *uniform agreement*: no two processes, correct or not, decide differently;
- *uniform integrity*: every process decides at most once; and
- *uniform validity*: every decided value was proposed by some process.

## Depends on

- [Failure detector classes](failure-detector-classes.md)
- [Reliable broadcast](../replication-and-consistency/reliable-broadcast.md)

## Sources

- T. D. Chandra and S. Toueg, "Unreliable failure detectors for reliable distributed systems", *Journal of the ACM* 43(2):225–267, 1996, Section 6.2, Figure 6, Lemma 6.2.1 and Theorem 6.2.3
