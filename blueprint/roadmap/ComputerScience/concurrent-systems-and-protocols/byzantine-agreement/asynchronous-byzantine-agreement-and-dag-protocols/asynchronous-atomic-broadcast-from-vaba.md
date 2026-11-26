# Asynchronous atomic broadcast from validated agreement

With $n \ge 3t + 1$ processes, a trusted threshold setup and secure threshold signatures, asynchronous Byzantine atomic broadcast (total-order broadcast of client requests with agreement, validity, total order and liveness) can be implemented by running a sequence of validated asynchronous Byzantine agreement instances (agreement on a value from an arbitrary domain that satisfies an externally checkable validity predicate), the $k$-th instance deciding a batch proposed by some process together with the signed request queues of $n - t$ distinct processes (hence of at least $t + 1$ correct processes) as its external-validity proof. With an expected-constant-round, expected-$O(n^2)$-word validated agreement, each delivered batch costs expected $O(n^2)$ words plus the batch dissemination cost.

## Proof sketch

Each process signs and disseminates its current queue of unordered requests and proposes the union of $n - t$ such signed queues from distinct processes; the external validity predicate checks these $n - t$ signatures. Agreement of each instance gives a common total order of batches, and liveness follows because a request held by all correct processes is eventually included in a decided batch, since every instance decides some correct process's valid proposal with constant probability and requests persist in correct queues until delivered.

## Depends on

- [Asynchronous binary Byzantine agreement and common coins](asynchronous-binary-byzantine-agreement.md)
- [Quorum certificate from threshold signatures](../linear-view-change-bft-state-machine-replication/quorum-certificate-threshold-signatures.md)

## Proof depends on

- [Validated asynchronous Byzantine agreement with optimal expected quadratic communication](validated-asynchronous-byzantine-agreement-optimal.md)

## Sources

- C. Cachin, K. Kursawe, F. Petzold, V. Shoup, "Secure and Efficient Asynchronous Broadcast Protocols", CRYPTO 2001.
- I. Abraham, D. Malkhi, A. Spiegelman, "Asymptotically Optimal Validated Asynchronous Byzantine Agreement", PODC 2019.
