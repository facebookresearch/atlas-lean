# Safety of stateful networks is undecidable under reverting FIFO semantics

Letting every middlebox nondeterministically reset to its initial state does not make safety verification of stateful networks decidable while channels stay FIFO.

**Theorem.** The safety verification problem for [stateful networks](stateful-networks-of-middleboxes.md) under the ordered (FIFO) reverting semantics is undecidable.

Without reverting, safety is undecidable for FIFO networks and EXPSPACE-complete for unordered ones (Velner et al., TACAS 2016, as cited by the source).

## Depends on

- [Stateful networks of middleboxes](stateful-networks-of-middleboxes.md)

## Proof depends on

None.

## Expansion

The proof simulates an arbitrary network under the ordinary FIFO semantics, whose safety (even isolation) is undecidable by Velner and coauthors, by a reverting network. Every middlebox gets auxiliary wake-up states and a wake-up packet type; its initial state is a wake-up state, in which it only forwards wake-up packets, marked with its own identity, and discards everything else. It leaves the wake-up phase, entering the original initial state, only after receiving confirmations that all other middleboxes are in wake-up states. Because channels are FIFO, at that point no ordinary packets remain in transit between middleboxes, so a revert of one middlebox amounts to a reset of the whole network and does not change which error states are reachable.

In contrast, when packet order is also abstracted away, the source's abstract interpretation loses no precision for middleboxes that may reset, so safety under the unordered reverting semantics is checked exactly by an algorithm polynomial in the size of the network and exponential only in the number of state queries per middlebox; that problem is still coNP-hard. The source also shows that when the number of hosts is not fixed no small-model bound on the number of hosts is computable, even for reverting networks with a single middlebox.

## Sources

- Kalev Alpernas, Roman Manevich, Aurojit Panda, Mooly Sagiv, Scott Shenker, Sharon Shoham and Yaron Velner, "Abstract Interpretation of Stateful Networks", in *Static Analysis (SAS 2018)*, Lecture Notes in Computer Science 11002, Springer, 2018, pp. 86–106, <https://doi.org/10.1007/978-3-319-99725-4_8>; read as arXiv:1708.05904v3, <https://arxiv.org/abs/1708.05904v3>: the theorem on ordered reverting networks in the subsection "Reverting Network Semantics", its proof in the appendix subsection "Undecidability of Safety of Reverting Networks Over Ordered Channels", and the appendix section "Networks with unbounded number of hosts", of that version.
