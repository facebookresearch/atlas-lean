# Trace refinement of labelled Markov decision processes is undecidable

One labelled Markov decision process refines another when every behavior of the first, measured by the probabilities of the label sequences it generates, can be reproduced by a strategy of the second. Deciding refinement is undecidable, already when the first process is a labelled Markov chain.

**Setting (Fijalkow, Kiefer and Shirmohammadi).** A *labelled Markov decision process* (MDP) $\mathcal{D} = \langle Q, \mu_0, L, \delta \rangle$ has a finite set of states $Q$, an initial distribution $\mu_0$ on $Q$, a finite set $L$ of labels and a finite relation $\delta$ assigning to each state a nonempty set of *moves*, each a probability distribution on $L \times Q$, with rational probabilities. Starting in a state drawn from $\mu_0$, at each step a controller chooses a move $m$ at the current state $q$, and with probability $m(a, q')$ the label $a$ is emitted and the next state is $q'$. A *strategy* maps each finite path to a probability distribution over the moves at its last state. A strategy $\alpha$ induces a *trace-probability function* $\mathrm{Tr}_{\mathcal{D}, \alpha}$ giving, for each finite word $w \in L^*$, the probability that the first $|w|$ labels emitted form $w$. A *labelled Markov chain* (MC) is an MDP with one move per state. For MDPs $\mathcal{D}$ and $\mathcal{E}$ over the same labels, $\mathcal{E}$ *refines* $\mathcal{D}$, written $\mathcal{D} \sqsubseteq \mathcal{E}$, if for every strategy $\alpha$ for $\mathcal{D}$ there is a strategy $\beta$ for $\mathcal{E}$ with $\mathrm{Tr}_{\mathcal{D}, \alpha} = \mathrm{Tr}_{\mathcal{E}, \beta}$.

**Theorem (Fijalkow, Kiefer and Shirmohammadi).** The problem $\mathsf{MC} \sqsubseteq \mathsf{MDP}$, which asks for an MC $\mathcal{D}$ and an MDP $\mathcal{E}$ whether $\mathcal{D} \sqsubseteq \mathcal{E}$, is undecidable. Hence the general problem $\mathsf{MDP} \sqsubseteq \mathsf{MDP}$ is undecidable.

This answers an open question of Doyen, Henzinger and Raskin. When $\mathcal{E}$ is an MC, refinement is decidable in NC, and the same paper studies the cases where $\mathcal{E}$ is restricted to memoryless or pure memoryless strategies.

## Depends on

- [Probabilistic automata and cut-point languages](../../../TheoryOfComputation/regular-languages/automata-and-expressions/weighted-automata-and-rational-series/probabilistic-automata-and-cut-point-languages.md)
- [Markov decision processes and adversaries](../../../Logic/temporal-logic/probabilistic-model-checking/markov-decision-processes-and-adversaries.md)
- [Markov decision process](../../heuristic-search-and-planning/value-iteration/mdp.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The emptiness problem for probabilistic automata is undecidable](../../../TheoryOfComputation/regular-languages/automata-and-expressions/weighted-automata-and-rational-series/emptiness-problem-for-probabilistic-automata.md)

## Expansion

The proof reduces the universality problem for probabilistic automata: whether every word over $\{a, b\}$ is accepted with probability at least $\frac{1}{2}$. Exchanging accepting and rejecting states turns this into the complement of the emptiness problem with cut-point $\frac{1}{2}$, which is undecidable. From an automaton $\mathcal{A}$ the authors build an MDP $\mathcal{D}(\mathcal{A})$ on the states of $\mathcal{A}$ and two new states $q_c, q_d$. In an accepting state there are two moves, each emitting $a$ or $b$ with probability $\frac{1}{4}$ while simulating $\mathcal{A}$ on that letter, and with the remaining probability $\frac{1}{2}$ emitting $c$ and moving to $q_c$, or emitting $d$ and moving to $q_d$; a non-accepting state has a single move that emits $a$ or $b$ in the same way and with probability $\frac{1}{2}$ emits $d$ and moves to $q_d$. A fixed MC $\mathcal{C}$ emits the letters with matching probabilities. Then $\mathcal{A}$ is universal exactly when $\mathcal{C} \sqsubseteq \mathcal{D}(\mathcal{A})$.

## Sources

- Nathanaël Fijalkow, Stefan Kiefer and Mahsa Shirmohammadi, *Trace Refinement in Labelled Markov Decision Processes*, Logical Methods in Computer Science 16(2), 2020, https://doi.org/10.23638/LMCS-16(2:10)2020; the definitions of labelled MDPs, strategies and trace refinement and the undecidability theorem in the section on undecidability results, read in arXiv:1510.09102v5. Locators in arXiv:1510.09102v5: Theorems 3.1 and 3.2.
