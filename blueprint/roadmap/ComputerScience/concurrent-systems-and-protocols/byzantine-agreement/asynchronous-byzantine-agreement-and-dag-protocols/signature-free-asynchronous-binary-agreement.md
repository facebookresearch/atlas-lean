# Signature-free asynchronous binary Byzantine agreement with O(n^2) messages per round

Assume $n \ge 3t + 1$ and a common coin. There is a signature-free asynchronous binary Byzantine agreement protocol in which every round consists of one binary-value broadcast and one auxiliary broadcast, so correct processes send $O(n^2)$ messages per round, and every correct process decides within an expected constant number of rounds. Hence the expected total message complexity is $O(n^2)$, which is optimal for asynchronous Byzantine agreement tolerating a linear number of faults.

## Proof sketch

In each round, processes run binary-value broadcast on their estimates, then broadcast one value from $\mathrm{bin\_values}$ and wait for $n - t$ auxiliary messages whose values are contained in $\mathrm{bin\_values}$. If the collected set is a singleton $\{b\}$, the process adopts $b$ and decides if $b$ equals the coin; otherwise it adopts the coin. Quorum intersection shows that at most one singleton value can be collected by correct processes in a round, so with probability $1/2$ per round the coin matches it and all correct processes converge, giving expected constant rounds.

## Depends on

- [Asynchronous binary Byzantine agreement and common coins](asynchronous-binary-byzantine-agreement.md)

## Proof depends on

- [Binary-value broadcast filters values proposed only by Byzantine processes](binary-value-broadcast.md)
- [Byzantine agreement requires quadratic communication](../linear-view-change-bft-state-machine-replication/dolev-reischuk-quadratic-lower-bound.md)

## Sources

- A. Mostéfaoui, H. Moumen, M. Raynal, "Signature-Free Asynchronous Binary Byzantine Consensus with t < n/3, O(n^2) Messages, and O(1) Expected Time", Journal of the ACM 62(4) (2015); PODC 2014.
- G. Bracha, "Asynchronous Byzantine Agreement Protocols", Information and Computation 75(2) (1987).
