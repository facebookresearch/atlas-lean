# HotStuff achieves optimistic responsiveness and linear view change

After GST, HotStuff commits a block in every view with a correct leader. A correct leader drives a decision with $O(n)$ authenticators of communication, including the view change, so the total communication to commit after GST following a sequence of $f$ faulty leaders is $O(f n)$ authenticators; and the protocol is optimistically responsive: once a correct leader is in place, it proceeds after receiving $n - f$ messages, at the speed of the actual network delay rather than the bound $\delta$. In contrast, PBFT-style view changes with two-phase commit require $\Omega(n^2)$ authenticators (or $O(n^3)$ without threshold signatures) per view change.

## Proof sketch

Each phase consists of one leader broadcast carrying a constant-size QC and $n$ votes sent back to the leader, i.e. $O(n)$ messages of constant size. The third phase is what removes the need for the new leader to justify its proposal with $n - f$ certificates: a replica locked on a block can be convinced by a single higher QC, because the extra phase guarantees that a QC higher than any lock exists among the $n - f$ new-view messages, so the leader waits only for those messages.

## Depends on

- [Chained HotStuff with locking and three-phase commit](hotstuff-protocol-three-phase.md)

## Proof depends on

- [Safety of HotStuff under n at least 3f + 1](hotstuff-safety.md)

## Sources

- M. Yin, D. Malkhi, M. K. Reiter, G. Golan Gueta, I. Abraham, "HotStuff: BFT Consensus with Linearity and Responsiveness", PODC 2019, arXiv:1803.05069.
