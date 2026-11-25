# Security with abort against malicious adversaries

Let $f$ be an $n$-party functionality and $\pi$ a protocol. In the ideal model with abort, honest parties send their inputs to a trusted party; the adversary, controlling a set $I$ of parties, may replace the inputs of $I$, receives the outputs of $I$, and then instructs the trusted party either to deliver outputs to the honest parties or to send them $\bot$. The protocol $\pi$ securely computes $f$ with abort against static malicious adversaries if for every probabilistic polynomial-time real adversary $A$ corrupting $I$ there is a probabilistic polynomial-time ideal adversary $S$ such that the joint distribution of the honest parties' outputs and the adversary's output in the real execution of $\pi$ with $A$ is computationally indistinguishable from that in the ideal model with $S$, for all inputs.

## Depends on

- [Two-party security against semi-honest adversaries](two-party-security-against-semi-honest.md)

## Sources

- D. Evans, V. Kolesnikov and M. Rosulek, *A Pragmatic Introduction to Secure Multi-Party Computation*, Foundations and Trends in Privacy and Security 2(2–3), 2018, <https://securecomputation.org/>
