# Execution-time opacity control of timed automata

A timed automaton with a private location is fully execution-time opaque when the durations of runs reaching a final location through the private location are exactly the durations of runs reaching it while avoiding that location. A controller that enables controllable actions over time tries to make the automaton opaque.

**Timed automata.** Clocks are real-valued variables that grow at rate $1$; a constraint over a finite set $X$ of clocks is a conjunction of inequalities $x \bowtie d$ with $x \in X$, $d \in \mathbb{Z}$ and ${\bowtie} \in \{<, \le, =, \ge, >\}$. A timed automaton (TA) is $\mathcal{A} = (\Sigma, L, \ell_0, \ell_{priv}, L_f, X, I, E)$ with a finite set $\Sigma$ of actions, a finite set $L$ of locations, an initial location $\ell_0$, a private location $\ell_{priv}$, a set $L_f \subseteq L \setminus \{\ell_{priv}\}$ of final locations, a finite set $X$ of clocks, an invariant constraint $I(\ell)$ for each location, and a finite set $E$ of edges $(\ell, g, a, R, \ell')$ with a guard constraint $g$, a label $a \in \Sigma \cup \{\epsilon\}$ ($\epsilon$ the silent action) and a set $R \subseteq X$ of clocks to reset. Final locations are urgent and have no outgoing edges. A state is a pair $(\ell, \nu)$ of a location and a clock valuation satisfying $I(\ell)$; time may elapse in a location while its invariant holds, and an edge may be taken when its guard holds, resetting the clocks in $R$ to $0$. A run starts in $(\ell_0, \mathbf{0})$ and alternates delays $d_i \ge 0$ and edges; its duration is the sum of its delays.

**Private and public runs.** A run ending in a final location is private if it visits $\ell_{priv}$ and public if it does not. Let $D^{priv}(\mathcal{A})$ and $D^{pub}(\mathcal{A})$ be the sets of durations of private and of public runs. $\mathcal{A}$ is fully execution-time opaque (fully ET-opaque) when $D^{priv}(\mathcal{A}) = D^{pub}(\mathcal{A})$.

**Strategies.** The actions are partitioned as $\Sigma = \Sigma_c \uplus \Sigma_u$ into controllable and uncontrollable actions. A strategy is a function $\sigma : \mathbb{R}_{\ge 0} \to 2^{\Sigma_c}$ giving, at each absolute time $t$, the set of enabled controllable actions. A run is compatible with $\sigma$ if every edge it takes at absolute time $t$ carries an action of $\sigma(t) \cup \Sigma_u$. With $D^{priv}_\sigma(\mathcal{A})$ and $D^{pub}_\sigma(\mathcal{A})$ the durations of compatible private and public runs, $\mathcal{A}$ is fully ET-opaque with $\sigma$ when $D^{priv}_\sigma(\mathcal{A}) = D^{pub}_\sigma(\mathcal{A})$. A strategy is finitely varying if every closed time interval splits into finitely many intervals on each of which $\sigma$ is constant.

**Strategy emptiness problem.** Given a TA $\mathcal{A}$ (with its partition of actions), decide whether the set of strategies $\sigma$ such that $\mathcal{A}$ is fully ET-opaque with $\sigma$ is empty.

## Depends on

None.

## Proof depends on

None.

## Expansion

Without control, full ET-opacity of a timed automaton is decidable. A meta-strategy fixes only finitely many strategy changes per time unit and weak ordering constraints between them, not their exact times; the existence of a meta-strategy making a TA fully ET-opaque is decidable in exponential space and such a meta-strategy can be built.

## Sources

- Étienne André, Marie Duflot, Laetitia Laversa and Engel Lefaucheux, "Execution-time opacity control for timed automata", *Software and Systems Modeling*, Springer, published online 2026 (no volume or pages in the publisher record read), doi:[10.1007/s10270-026-01395-5](https://doi.org/10.1007/s10270-026-01395-5); extended version of the paper of the same title in *Software Engineering and Formal Methods (SEFM 2024)*, Lecture Notes in Computer Science 15280, pp. 347–365, 2024, doi:[10.1007/978-3-031-77382-2_20](https://doi.org/10.1007/978-3-031-77382-2_20). Read in arXiv:2409.10336v3 ([arXiv](https://arxiv.org/abs/2409.10336v3)), the extended version of the conference paper; the journal article was not read: Definitions 1 and 2 (timed automata and their semantics), Assumption 1, Definition 5 (full ET-opacity), Definition 6 (semantics of a controlled TA), Definition 7 (full ET-opacity with a strategy), Definition 8 (finitely varying strategies) and the strategy emptiness problem of Section 3, in the numbering of that version.
