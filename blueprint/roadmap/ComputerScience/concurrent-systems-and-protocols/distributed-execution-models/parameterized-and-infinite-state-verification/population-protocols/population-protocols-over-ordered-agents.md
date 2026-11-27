# Whether a population protocol over ordered agents is a decider is undecidable

For population protocols whose finite-state agents are totally ordered and whose transitions may test the agents' relative positions, it is undecidable whether the protocol always stabilizes to a consensus, already when the only test is the order $<$, or immediate-observation protocols use the successor relation; for classical unordered protocols the question is decidable.

**Setting (Blondin, Cadilhac, Courchesne, Guillou, Mascle and Vialard).** For a set $\mathcal N \subseteq 2^{\mathbb N \times \mathbb N}$ of *numerical predicates*, a population protocol in $\mathrm{PP}[\mathcal N]$ is $(Q, \Sigma, O, \Delta)$ with finitely many states $Q$, initial states $\Sigma \subseteq Q$, an opinion map $O : Q \to \{\top, \bot\}$, and transitions $q_1, q_2 \xrightarrow{P} q_3, q_4$ with $P \in \mathcal N$ or $P$ always true. A configuration is a word in $Q^+$, one state per agent in the order of the agents; a transition lets two distinct agents at positions $i$ and $j$ with $(i, j) \in P$, in states $q_1$ and $q_2$, move to $q_3$ and $q_4$. Initial configurations are words in $\Sigma^+$. A configuration is a *$b$-consensus* if all its states have opinion $b$, and *$b$-stable* if every configuration reachable from it is a $b$-consensus. A run is *fair* if every configuration reachable from a configuration that occurs infinitely often also occurs infinitely often. The protocol is a *decider* (also called well specified) if for every initial configuration $w$ there is $b \in \{\top, \bot\}$ such that every fair run from $w$ visits a $b$-stable configuration. A protocol is *immediate-observation* if each transition changes the state of at most one agent; these form $\mathrm{IOPP}[\mathcal N]$. The predicate $<$ is $\{(i, j) : i < j\}$ and $+1$ is $\{(i, i + 1)\}$.

**Theorem (Blondin, Cadilhac, Courchesne, Guillou, Mascle and Vialard).** It is undecidable whether a given protocol of $\mathrm{PP}[<]$ is a decider, and likewise for $\mathrm{IOPP}[+1]$ and $\mathrm{PP}[+1]$.

For classical population protocols $\mathrm{PP}[\emptyset]$, being a decider is decidable (Esparza, Ganty, Leroux and Majumdar). For $\mathrm{IOPP}[<]$ the same paper shows the question decidable assuming a natural conjecture.

## Depends on

- [Decidability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)
- [Emptiness of a linear bounded automaton on computable input slices is undecidable](../../../../../TheoryOfComputation/undecidable-problems/emptiness-problem-for-linear-bounded-automata/exists-is-lba-not-computable-pred-forall.md)

## Expansion

The *emptiness problem* asks whether some initial configuration of a protocol can reach a $\top$-stable configuration. It reduces to the complement of the decider property: add a fresh sink state $q_\bot$ with opinion $\bot$ and let every agent with opinion $\bot$ move to it. Then every configuration containing a $\bot$-agent can be driven to the $\bot$-stable consensus $q_\bot^\ast$, while a reachable $\top$-stable configuration stays $\top$-stable, so the new protocol is a decider exactly when the old one has empty language; the construction preserves immediate observation. Emptiness is undecidable for $\mathrm{IOPP}[+1]$, and hence for $\mathrm{PP}[+1]$, because such protocols simulate linear bounded automata, and it is undecidable for $\mathrm{PP}[<]$ by a reduction from Post's correspondence problem.

## Sources

- Michael Blondin, Michaël Cadilhac, Benjamin Courchesne, Lucie Guillou, Corto Mascle and Isa Vialard, "Population Protocols over Ordered Agents", in *53rd International Colloquium on Automata, Languages, and Programming (ICALP 2026)*, Leibniz International Proceedings in Informatics 374, Schloss Dagstuhl, 2026, article 167, doi:[10.4230/LIPIcs.ICALP.2026.167](https://doi.org/10.4230/LIPIcs.ICALP.2026.167); read in arXiv:2605.09937v1 ([arXiv](https://arxiv.org/abs/2605.09937v1)), cited by section: Section 2 (population protocols over ordered agents, consensus, stability, fairness, deciders), Section 6 (the simulation of linear-space machines by $\mathrm{IOPP}[+1]$), and Section 7 (the reduction from emptiness, the corollary for $\mathrm{IOPP}[+1]$ and $\mathrm{PP}[+1]$, the theorem for $\mathrm{PP}[<]$, and the conditional decidability for $\mathrm{IOPP}[<]$).
