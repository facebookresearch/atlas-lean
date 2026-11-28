# Asynchronous common subset from n reliable broadcasts and n binary agreements

With $n \ge 3t + 1$, the following protocol (Ben-Or, Kelmer and Rabin; HoneyBadgerBFT, Figure 4) solves asynchronous common subset: every process reliably broadcasts its input; process $i$, upon delivering process $j$'s broadcast, inputs $1$ to the $j$-th instance of binary Byzantine agreement if it has not yet provided an input to that instance; once $n - t$ binary agreement instances have decided $1$, process $i$ inputs $0$ to every instance to which it has not yet provided an input; once all $n$ instances have decided, it outputs the broadcast values of all $j$ whose instance decided $1$, waiting to deliver them. Both rules matter: without the check, a delayed broadcast could deliver after the process already input $0$, and outputting after only the first $n - t$ decisions could miss later decisions of $1$. Instantiated with the Mostéfaoui–Moumen–Raynal binary agreement driven by a threshold-signature common coin, and erasure-coded reliable broadcast, the expected communication per epoch is $O(n^2 \ell + \lambda n^3 \log n)$ bits for inputs of $\ell$ bits and security parameter $\lambda$.

For HoneyBadgerBFT's atomic broadcast, the amortized cost must distinguish proposed from delivered transactions: each process proposes $B/n$ transactions chosen at random from the first $B$ of its queue, so proposals may overlap. Assuming every correct process's queue holds at least $B$ distinct transactions, the expected number of distinct transactions committed per epoch is at least $B/4$ (Theorem 3), so with batch size $B = \Omega(\lambda n^2 \log n)$ the amortized communication is $O(n)$ per committed transaction.

## Proof sketch

Totality: suppose $n - t$ correct processes receive an input, and consider the stage before any correct process has input $0$ to any instance. In that stage every correct process inputs $1$ to the instance of each correct sender whose broadcast it delivers; the $n - t$ broadcasts of the correct processes with inputs are eventually delivered by every correct process, so unless $n - t$ instances have already decided $1$, these $n - t$ instances receive input $1$ from all correct processes and, by validity, decide $1$. Either way $n - t$ instances decide $1$, after which every correct process provides inputs to all remaining instances, and all $n$ instances terminate. Agreement on the set follows from agreement of each binary instance, and validity from the $n - t$ decisions of $1$, at most $t$ of which belong to Byzantine senders. A decision of $1$ implies, by validity, that some correct process input $1$ and hence delivered that broadcast, so by the totality of reliable broadcast every correct process eventually delivers the value.

## Depends on

- [Asynchronous common subset](asynchronous-common-subset.md)
- [Asynchronous binary Byzantine agreement and common coins](asynchronous-binary-byzantine-agreement.md)

## Proof depends on

- [Signature-free asynchronous binary Byzantine agreement with O(n^2) messages per round](signature-free-asynchronous-binary-agreement.md)
- [Bracha's Byzantine reliable broadcast](../../replication-and-consistency/bracha-s-byzantine-reliable-broadcast.md)

## Sources

- M. Ben-Or, B. Kelmer, T. Rabin, "Asynchronous Secure Computations with Optimal Resilience", PODC 1994.
- A. Miller, Y. Xia, K. Croman, E. Shi, D. Song, "The Honey Badger of BFT Protocols", ACM CCS 2016, IACR ePrint 2016/199, Sections 4.3–4.4 (Section 4.4: binary agreement of Mostéfaoui et al. with a threshold-cryptography common coin), Figure 4 and Theorems 2–3.
- S. Das, Z. Xiang, L. Ren, "Asynchronous Data Dissemination and its Applications", ACM CCS 2021.
