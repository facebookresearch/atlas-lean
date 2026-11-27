# Byzantine agreement with subquadratic total communication against an adaptive adversary

Consider the synchronous model in which every pair of processors is joined by a private, authenticated channel (the recipient learns the sender's identity and no one else sees the message), every processor has private randomness, and there are no other cryptographic assumptions; the adversary is adaptive and rushing, may corrupt processors at any time up to a $(1/3 - \varepsilon)$ fraction for a constant $\varepsilon > 0$, and corrupted processors may send any number of messages. Then there is a randomized protocol that with high probability (probability at least $1 - n^{-c}$ for every constant $c$ and large $n$) is correct, that is, all good processors terminate and agree on a bit that was the input of some good processor, runs in polylogarithmic time, and in which each good processor sends $\tilde O(\sqrt n)$ bits, for $\tilde O(n^{3/2})$ total communication. This breaks the $\Omega(n^2)$ barrier that holds for deterministic protocols; correctness, time and communication bounds all hold with high probability, not with certainty.

## Proof sketch

First, processors compete in local elections in a tournament tree over a sparse network, with secrets shared in arrays that cannot be reconstructed until they are used; this yields almost-everywhere Byzantine agreement, in which all but a $1/\log n$ fraction of good processors agree on a good processor's input, together with an almost-everywhere global coin subsequence (Theorems 2 and 3). Second, an almost-everywhere-to-everywhere protocol amplifies this agreement to all good processors (Theorem 4): uninformed processors query random processors, and responses are filtered with the global coins so that the adaptive adversary cannot flood or predict the queries; private channels and private randomness are what prevent the adversary from learning where communication will occur. Merely having arbitrary pairs of processors exchange random $\sqrt n$-size samples would not suffice, since two such samples need not share many good processors.

## Depends on

- [Reaching Byzantine agreement](../solves.md)
- [Fail-stop, omission and Byzantine faults](../../distributed-execution-models/fail-stop-omission-and-byzantine-faults.md)

## Sources

- V. King, J. Saia, "Breaking the O(n^2) Bit Barrier: Scalable Byzantine Agreement with an Adaptive Adversary", Journal of the ACM 58(4) (2011); PODC 2010; arXiv:1002.4561, Section 1.1 and Theorems 1–4.
