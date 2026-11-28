# Safety of stateful networks is undecidable under reverting FIFO semantics

Letting every middlebox nondeterministically reset to its initial state does not make safety verification of stateful networks decidable while channels stay FIFO.

**Theorem.** The safety verification problem for [stateful networks](stateful-networks-of-middleboxes.md) under the ordered (FIFO) reverting semantics is undecidable.

Without reverting, safety is undecidable for FIFO networks and EXPSPACE-complete for unordered ones (Velner et al., TACAS 2016, as cited by the source).

## Depends on

- [Stateful networks of middleboxes](stateful-networks-of-middleboxes.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof uses that an automaton with a FIFO channel of messages (a channel machine) can simulate a Turing machine, the channel storing the tape; without reverting this already makes isolation over ordered channels undecidable for one host and one middlebox with a self-loop. To handle reverting, the middlebox gets an auxiliary packet type and auxiliary states: whenever it is in its initial state it sends a special packet over its self-loop and discards all arriving packets until that special packet returns, which empties the self-loop, so a revert resets the simulated tape together with the machine. Hence isolation fails exactly when the Turing machine reaches an accepting state. A good expansion links the simulation of Turing machines by channel machines with one FIFO channel.

In contrast, when packet order is also abstracted away, the source's abstract interpretation loses no precision for middleboxes that may reset, so safety under the unordered reverting semantics is checked exactly by an algorithm polynomial in the size of the network and exponential only in the number of state queries per middlebox; that problem is still coNP-hard. The source also shows that when the number of hosts is not fixed no small-model bound on the number of hosts is computable, even for reverting networks with a single middlebox.

## Sources

- Kalev Alpernas, Roman Manevich, Aurojit Panda, Mooly Sagiv, Scott Shenker, Sharon Shoham and Yaron Velner, "Abstract Interpretation of Stateful Networks", in *Static Analysis (SAS 2018)*, Lecture Notes in Computer Science 11002, Springer, 2018, pp. 86–106, <https://doi.org/10.1007/978-3-319-99725-4_8>; read as arXiv:1708.05904v3, <https://arxiv.org/abs/1708.05904v3>: Theorem 2(ii) in Section 3.3 ("Unordered and Reverting Network Semantics"), its proof in Appendix B, Theorem 2(iii), and Theorem 5 in Appendix F ("Networks with unbounded number of hosts"), in the numbering of that version.
