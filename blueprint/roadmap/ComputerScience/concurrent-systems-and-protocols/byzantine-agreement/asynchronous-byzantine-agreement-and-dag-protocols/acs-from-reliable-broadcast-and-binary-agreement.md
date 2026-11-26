# Asynchronous common subset from n reliable broadcasts and n binary agreements

With $n \ge 3t + 1$, the following protocol solves asynchronous common subset: every process reliably broadcasts its input; process $i$ inputs $1$ to the $j$-th instance of binary Byzantine agreement as soon as it delivers process $j$'s broadcast; once $n - t$ binary agreement instances have decided $1$, process $i$ inputs $0$ to all instances it has not yet joined; finally it outputs the broadcast values of all $j$ whose instance decided $1$, waiting to deliver them. Instantiated with signature-free binary agreement and erasure-coded reliable broadcast, the expected communication per epoch is $O(n^2 \ell + \lambda n^3 \log n)$ bits for inputs of $\ell$ bits and security parameter $\lambda$, so atomic broadcast with batches of size $\Omega(n \log n)$ has amortized $O(n)$ communication per transaction.

## Proof sketch

Termination: at least $n - t$ correct broadcasts are eventually delivered by every correct process, so at least $n - t$ agreement instances eventually receive input $1$ from all correct processes and, by validity, decide $1$; then all remaining instances receive inputs and terminate. Agreement on the set follows from agreement of each binary instance, and a decision of $1$ implies some correct process delivered that broadcast, so by the totality of reliable broadcast every correct process eventually delivers the value.

## Depends on

- [Asynchronous common subset](asynchronous-common-subset.md)
- [Asynchronous binary Byzantine agreement and common coins](asynchronous-binary-byzantine-agreement.md)

## Proof depends on

- [Signature-free asynchronous binary Byzantine agreement with O(n^2) messages per round](signature-free-asynchronous-binary-agreement.md)
- [Bracha's Byzantine reliable broadcast](../../replication-and-consistency/bracha-s-byzantine-reliable-broadcast.md)

## Sources

- M. Ben-Or, B. Kelmer, T. Rabin, "Asynchronous Secure Computations with Optimal Resilience", PODC 1994.
- A. Miller, Y. Xia, K. Croman, E. Shi, D. Song, "The Honey Badger of BFT Protocols", ACM CCS 2016.
- S. Das, Z. Xiang, L. Ren, "Asynchronous Data Dissemination and its Applications", ACM CCS 2021.
