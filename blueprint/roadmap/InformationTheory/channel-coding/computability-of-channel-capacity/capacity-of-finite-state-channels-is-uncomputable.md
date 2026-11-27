# The capacity of finite-state channels cannot be approximated by any algorithm

No algorithm approximates the capacity of finite-state channels with rational transition probabilities to within $1/5$; for each rational $\lambda$ there is a family of such channels, each of capacity at least $\lambda$ or at most $\lambda/2$, on which it is undecidable which holds.

Let finite-state channels in product form and their capacity be as in [Finite-state channels and their capacity](finite-state-channels.md). Consider channels with a fixed, known initial state, rational transition probabilities $p(y \mid x, s')$ and $q(s \mid x, s')$, binary output and information stable behavior, so that the capacity is the limit of the mutual information rate.

**Theorem (Elkouss and Pérez-García).**

1. Any function that, on input the probability assignments $\{p(y \mid x, s'), q(s \mid x, s')\}$ of an information stable finite-state channel $\mathbf{N}$ with $10$ input symbols and $62$ states, outputs a rational number $c$ with $|C(\mathbf{N}) - c| \le 1/5$ is uncomputable (Main Result 1 of the source).
2. For every rational $\lambda \in (0, 1]$ there is an explicit family $\mathcal{S}_\lambda$ of such channels, each with capacity $\ge \lambda$ or $\le \lambda/2$, for which it is undecidable, given $\mathbf{N} \in \mathcal{S}_\lambda$, which of the two holds (Main Result 2).

The same holds for any larger numbers of input symbols and states, for example $4$ input bits, $1$ output bit and $6$ bits of memory, and for every more general class of channels with memory.

## Depends on

- [Finite-state channels and their capacity](finite-state-channels.md)

## Proof depends on

- [The emptiness problem for probabilistic automata is undecidable](../../../TheoryOfComputation/regular-languages/automata-and-expressions/weighted-automata-and-rational-series/emptiness-problem-for-probabilistic-automata.md)

## Expansion

From a [probabilistic finite automaton](../../../TheoryOfComputation/regular-languages/automata-and-expressions/weighted-automata-and-rational-series/probabilistic-automata-and-cut-point-languages.md) $\mathcal{A}$, extended by an identity letter and a reset letter, the source builds a channel $\mathbf{V}_{\mathcal{A}}$ with a data input and a control input: the control input drives $\mathcal{A}$, whose state is the channel state, and the data bit is transmitted noiselessly when $\mathcal{A}$ is in an accepting state and replaced by a uniformly random bit otherwise. Its capacity equals the value of $\mathcal{A}$, the supremum of the acceptance probabilities of words (Theorem 1 of the source). A construction of Gimbert and Oualhadj turns undecidability of emptiness for cut-point languages, in Hirvensalo's form for automata with $2$ letters and $27$ states (Corollary 2 of the source), into a family of automata whose value is at least $\lambda$ or at most $\lambda/2$ with no algorithm telling which (Lemma 1), and Main Result 1 is the case $\lambda = 1$. The capacity formula, the Gimbert–Oualhadj gap construction and Hirvensalo's fixed-size version have no pages.

## Sources

- D. Elkouss and D. Pérez-García, "Memory effects can make the transmission capability of a communication channel uncomputable", Nature Communications 9 (2018), article 1149, https://doi.org/10.1038/s41467-018-03428-0; read in arXiv:1601.06101v3 (Main Results 1 and 2, Lemma 1, Theorem 1 and the supplementary section proving Lemma 1, with Corollary 2, of arXiv:1601.06101v3).
