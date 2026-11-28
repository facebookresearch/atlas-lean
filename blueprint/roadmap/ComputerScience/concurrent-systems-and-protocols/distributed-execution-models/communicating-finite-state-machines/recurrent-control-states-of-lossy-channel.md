# Recurrent control-state reachability for lossy channel systems is undecidable

Whether a lossy channel system has a computation that visits a given control state infinitely often is undecidable, already for systems with a single channel, although reachability of control states is decidable.

**Recurrent state problem.** Given a [lossy channel system](lossy-channel-systems.md) $L$ and a control state $s$ of $L$, decide whether $L$ has a computation that visits $s$ infinitely often (a global state with control state $s$ occurs at infinitely many positions). Write $n$-RSP for the restriction to systems with at most $n$ channels.

**Theorem (Abdulla and Jonsson).** The recurrent state problem is undecidable (Corollary 4.3); it is undecidable already for lossy channel systems with two channels (the construction of Theorem 4.2) and with one channel: 1-RSP is undecidable (Theorem 4.4).

By contrast, reachability of a control state or of a finite set of global states is decidable for lossy channel systems (Theorem 3.1).

## Depends on

- [Lossy channel systems](lossy-channel-systems.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The reduction is from the cyclic Post correspondence problem, shown undecidable by Ruohonen: given pairs $(x_i, y_i)$, is there a nonempty index sequence with $x_{i_1} \cdots x_{i_m}$ a cyclic shift of $y_{i_1} \cdots y_{i_m}$? A system with two channels repeatedly guesses indices and transforms the contents of its two channels by the chosen words, returning to a checking control state $s_1$ after each checking cycle. If the instance has a solution, a computation can repeat the checking cycle forever and visit $s_1$ infinitely often; if it has none, every computation reaching $s_1$ eventually deadlocks without visiting $s_1$ infinitely often (Theorem 4.2). For one channel, the two channels are merged into one and the receptions of messages not at the head are simulated by cycling the channel contents. A good expansion links a page for the undecidability of the cyclic Post correspondence problem.

## Sources

- Parosh Aziz Abdulla and Bengt Jonsson, "Undecidable verification problems for programs with unreliable channels", in *Automata, Languages and Programming (ICALP 1994)*, Lecture Notes in Computer Science 820, Springer, 1994, pp. 316–327, doi:10.1007/3-540-58201-0_78; read in the authors' archived copy at <https://www.it.uu.se/research/docs/fm/apv/publications/files/icalp94.ps>: Section 4 (Theorem 4.1, Theorem 4.2 and its proof idea, Corollary 4.3 and Theorem 4.4) and Theorem 3.1 of that copy; the full proofs are deferred to the journal version.
- Parosh Aziz Abdulla and Bengt Jonsson, "Undecidable verification problems for programs with unreliable channels", *Information and Computation* 130(1):71–90, 1996, doi:10.1006/inco.1996.0083 (the journal version; not read).
