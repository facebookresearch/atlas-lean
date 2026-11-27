# Almost-sure opacity and disclosure problems for POMDPs are undecidable

When a system is a partially observable Markov decision process resolved by observation-based schedulers and the secret is an ω-regular set of runs, the qualitative and quantitative questions about how likely an observer is to learn the secret are undecidable, although they are all decidable under perfect observation.

**Setting (Bérard, Chatterjee and Sznajder).** A *Markov decision process* (MDP) is a tuple $\mathcal{A} = (Q, \Sigma, \mathit{Act}, \Delta, q_0)$ with a finite set $Q$ of states, a finite set $\mathit{Act}$ of actions, a finite alphabet $\Sigma$ of transition labels, a partial transition function $\Delta : Q \times \mathit{Act} \to \mathcal{D}(\Sigma \times Q)$ and an initial state $q_0$. A run is a sequence $q_0 (\alpha_0, a_0) q_1 (\alpha_1, a_1) q_2 \cdots$ with each $\alpha_i$ enabled in $q_i$ and $\Delta(q_i, \alpha_i)(a_i, q_{i+1}) > 0$; $\mathrm{Runs}(\mathcal{A})$ is the set of infinite runs. A *scheduler* maps each finite run to a distribution on actions enabled in its last state; it has *finite memory* if it is given by a finite set of memory states with an initial memory state, a choice function and a memory update. A scheduler $\sigma$ induces a probability measure $\mathbb{P}_\sigma$ on $\mathrm{Runs}(\mathcal{A})$. A *POMDP* is an MDP with an equivalence relation $\sim$ on $Q$ such that equivalent states enable the same actions, and an *observation-based scheduler* ($\sim$-scheduler) takes the same decision on two finite runs of equal length with the same actions whose state sequences are pointwise equivalent.

The *secret* is a set $\varphi \subseteq \mathrm{Runs}(\mathcal{A})$ given by a deterministic automaton over the alphabet $Q \cup (\mathit{Act} \times \Sigma)$ with a Büchi (DBA), co-Büchi (DCA) or parity (DPA) acceptance condition. The *observation function* is the morphism $\mathcal{O}$ on runs induced by a map $Q \cup (\mathit{Act} \times \Sigma) \to \Gamma \cup \{\varepsilon\}$ for a finite alphabet $\Gamma$. With $\overline{\varphi} = \mathrm{Runs}(\mathcal{A}) \setminus \varphi$, the secret is *opaque* if $\varphi \subseteq \mathcal{O}^{-1}(\mathcal{O}(\overline{\varphi}))$: every run in the secret is observationally equivalent to one outside it. The *probabilistic disclosure* under a scheduler $\sigma$ is

$$
\mathrm{PrDiscl}_\sigma(\varphi, \mathcal{A}, \mathcal{O}) = \mathbb{P}_\sigma\bigl(\varphi \setminus \mathcal{O}^{-1}(\mathcal{O}(\overline{\varphi}))\bigr),
$$

the probability of runs whose observation reveals that the secret holds, and $\mathrm{PrDiscl}(\varphi, \mathcal{A}, \mathcal{O})$ is its supremum over schedulers ($\sim$-schedulers for a POMDP). The decision problems are: the *value problem* (compute $\mathrm{PrDiscl}$); the *general disclosure problem* (given $\delta \in [0, 1]$, is $\mathrm{PrDiscl} > \delta$?); the *almost-sure opacity problem* (is $\mathrm{PrDiscl} = 0$?); the *limit disclosure problem* (is $\mathrm{PrDiscl} = 1$?); and the *almost-sure disclosure problem* (is there a scheduler $\sigma$ with $\mathrm{PrDiscl}_\sigma = 1$?). Each can be restricted to finite-memory schedulers.

**Theorem (Bérard, Chatterjee and Sznajder).** Given a POMDP $\mathcal{A}$ and a morphism $\mathcal{O}$ as observation function:

1. the almost-sure disclosure problem is undecidable for secrets given as DCA or DPA;
2. the almost-sure opacity problem is undecidable for secrets given as DBA or DPA;
3. the limit disclosure problem, the general disclosure problem and the value problem are undecidable for secrets given as DBA, DCA or DPA, both with general and with finite-memory schedulers.

For MDPs with perfect observation and secrets given as DPA, the value is computable and all five problems are decidable (Theorem 10 and Corollaries 11 and 12 of the copy read). For POMDPs, almost-sure disclosure with a secret given as a DBA is EXPTIME-complete (Theorem 14), and the finite-memory almost-sure opacity and almost-sure disclosure problems for secrets given as DPA are EXPTIME-complete (Theorem 15).

## Depends on

- [Markov decision processes and adversaries](../../../Logic/temporal-logic/probabilistic-model-checking/markov-decision-processes-and-adversaries.md)
- [Finite POMDPs](../../heuristic-search-and-planning/partially-observable-planning/finite-pomdps.md)
- [Büchi acceptance condition](../../../TheoryOfComputation/omega-automata-and-games/emptiness-of-b-chi-automata/mem-language-iff.md)
- [Nondeterministic parity automaton](../../../TheoryOfComputation/omega-automata-and-games/parity-automata/parity.md)

## Proof depends on

- [The emptiness problem for probabilistic automata is undecidable](../../../TheoryOfComputation/regular-languages/automata-and-expressions/weighted-automata-and-rational-series/emptiness-problem-for-probabilistic-automata.md)
- [The value-1 problem for probabilistic automata is undecidable](../../../TheoryOfComputation/regular-languages/automata-and-expressions/weighted-automata-and-rational-series/value-1-problem-for-probabilistic-automata.md)

## Expansion

The proof reduces qualitative questions about POMDPs with a Büchi or co-Büchi condition $\mathrm{Acc}(F)$ to disclosure. From a POMDP $\mathcal{A}$ one builds $\mathcal{A}'$ with a new initial state that moves with probability $\frac{1}{2}$ each, under new labels $a_1$ and $a_2$, into two copies $\mathcal{A}_1$ and $\mathcal{A}_2$ of $\mathcal{A}$, the equivalence identifying copies of the same state. The secret consists of the runs through $\mathcal{A}_1$ satisfying $\mathrm{Acc}(F_1)$ together with all runs through $\mathcal{A}_2$, and the observation forgets which copy was entered. Observation-based schedulers of $\mathcal{A}$ and $\mathcal{A}'$ correspond, with $\mathrm{PrDiscl}_{\sigma'}(\varphi, \mathcal{A}', \mathcal{O}) = \mathbb{P}_\sigma(\mathrm{Acc}(F))$. Hence positive, almost-sure and limit-sure winning for Büchi and co-Büchi conditions in POMDPs transfer to the disclosure problems. A good expansion links pages for the undecidability results this transfer uses: almost-sure winning for co-Büchi conditions and positive winning for Büchi conditions in POMDPs (Baier, Größer and Bertrand; Chatterjee, Doyen, Gimbert and Henzinger), and limit-sure winning, through the probabilistic automata results linked above, which also hold for finite-memory schedulers.

## Sources

- Béatrice Bérard, Krishnendu Chatterjee and Nathalie Sznajder, "Probabilistic opacity for Markov decision processes", Information Processing Letters 115(1), pp. 52–59, 2015, <https://doi.org/10.1016/j.ipl.2014.09.001>; read in arXiv:1407.4225v2, <https://arxiv.org/abs/1407.4225v2>: Definitions 5–8 (POMDPs, observation-based schedulers, opacity, probabilistic disclosure), the five problems of Section 3, Theorem 10, Corollaries 11 and 12, Theorem 13 (main statement), Theorems 14 and 15, numbered as in arXiv:1407.4225v2.
