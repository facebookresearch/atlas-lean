# Model checking the probabilistic trust logic PRTL* is undecidable

The logic PRTL* adds belief and cognitive-trust operators to probabilistic branching-time logic over partially observable stochastic multiagent systems; its model checking problem is undecidable, even for a single agent and with trivial guarding of goals and intentions.

**Models.** An *autonomous stochastic multiagent system* (ASMAS) has a finite set of agents, a finite set of states with an initial distribution, finite action sets for each agent, a probabilistic transition function on joint actions, a labeling of states by atomic propositions, and for each agent a set of observations with an observation function, so each agent sees the system only through its observations. Each agent also has a cognitive structure (goals and intentions, with cognitive strategies choosing their changes) and preference functions; an agent's *belief* is a probability distribution over execution histories, the conditional probability of each history given the agent's observation sequence (Definition 15). Observations distinguish transition types: two histories with the same observation sequence for an agent have the same type sequence for it (Assumption 4), which places the histories conditioned on in one probability space.

**Finite presentation.** A cognitive strategy in Definition 12 is a function on all finite histories and need not have a finite description. For model checking, the source replaces this structure $\Pi$ by a finite guarding mechanism $\Lambda$ (Section 9, Definition 22; opening of Section 10): each agent has a goal guard function, which assigns formulas to sets of goals, and an intention guard function, which assigns formulas to pairs of an intention and a set of goals. These formulas belong to the language $\mathcal L_A(\mathrm{PRTL}^*)$, whose belief and trust formulas are threshold tests such as $\mathtt B_A^{\bowtie q}\psi$ or, in their quantitative variants, queries that return the value of the probability or expectation. The cognitive strategies are then derived from $\Lambda$ by pro-attitude synthesis (Section 9); they are not additional input. The system also satisfies Assumption 2: each agent's cognitive state determines its next action, so the transition function, not the agents, supplies the randomness of successor states. When every guard is constantly true, the guarding mechanism is called *trivial*.

**Logic.** Formulas of PRTL* are given by

$$
\phi::=p\mid\neg\phi\mid\phi\lor\phi\mid\forall\psi\mid\mathtt P^{\bowtie q}\psi\mid\mathtt G_A\phi\mid\mathtt I_A\phi\mid\mathtt C_A\phi\mid\mathtt B_A^{\bowtie q}\psi\mid\mathtt{CT}_{A,B}^{\bowtie q}\psi\mid\mathtt{DT}_{A,B}^{\bowtie q}\psi,
$$

$$
\psi::=\phi\mid\neg\psi\mid\psi\lor\psi\mid\mathtt X\psi\mid\psi\,\mathtt U\,\psi,
$$

with $p$ an atomic proposition, $A,B$ agents, $\bowtie\in\{<,\le,>,\ge\}$ and $q\in[0,1]$. Here $\mathtt B_A^{\bowtie q}\psi$ says that agent $A$ believes $\psi$ with probability $\bowtie q$, and $\mathtt{CT}_{A,B}^{\bowtie q}\psi$ and $\mathtt{DT}_{A,B}^{\bowtie q}\psi$ express competence trust and disposition trust of $A$ in $B$ for the task $\psi$; $\mathtt G_A\phi$ and $\mathtt I_A\phi$ say that $\phi$ holds after every possible change of $A$'s goal, respectively intention (those in the support of $A$'s cognitive strategies), and $\mathtt C_A\phi$ that $\phi$ holds after some change of $A$ to a legal intention (Definition 10). $\mathtt B_A^{\bowtie q}\psi$ holds when the expectation, under $A$'s belief, of the max–min (for $\ge, >$) or min–max (for $<, \le$) probability of $\psi$ over the agents' strategies, from each history, is $\bowtie q$ (Definition 17); the trust operators are defined similarly. The *model checking problem* asks, given a finite ASMAS satisfying Assumption 2, presented with its guarding mechanism $\Lambda$, and a formula, whether the formula holds in every state in the support of the initial distribution (Theorem 12). Instances are finite, with rational probabilities and thresholds $q$. The proof (Appendix A of the source) reduces the emptiness and strict emptiness problems of probabilistic automata, which are undecidable already with rational transition probabilities and rational thresholds.

**Theorem (Huang, Kwiatkowska and Olejnik).** Model checking PRTL* over ASMAS is undecidable, even if the guarding mechanism is trivial (Theorem 5 of the source).

The source also shows that the synthesis of pro-attitude functions whose formulas are in the language $\mathcal L_A(\mathrm{PRTL}^*)$ is undecidable (Theorem 4); this language consists of the Boolean combinations of atomic propositions and of belief and trust formulas of agent $A$ whose path formulas contain no temporal operators.

Both problems remain undecidable for formulas concerning the beliefs of a single agent. The source identifies decidable fragments, among them a bounded fragment whose model checking problem is in EXPTIME.

## Depends on

- [Discrete-time Markov chains](../discrete-time-markov-chains.md)
- [Markov decision processes and adversaries](../markov-decision-processes-and-adversaries.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The emptiness problem for probabilistic automata is undecidable](../../../../TheoryOfComputation/regular-languages/automata-and-expressions/weighted-automata-and-rational-series/emptiness-problem-for-probabilistic-automata.md)

## Expansion

Theorem 5 reduces from the emptiness and strict emptiness problems of probabilistic automata, which are undecidable (the source cites Paz's book for this): given a probabilistic automaton $(Q, A, (M_a)_{a \in A}, q_0, F)$ and a cut-point $\epsilon$, is there a word $w$ with $M_w(\Delta_0)(F) \ge \epsilon$ (respectively $> \epsilon$), where $\Delta_0$ is concentrated on $q_0$? The source builds a single-agent ASMAS with states $A \times Q$, initial state $(a_0, q_0)$ for a fixed letter $a_0$ with a Dirac initial distribution, one action $\tau$, and transitions $T((a,q),\tau,(a',q')) = M_{a'}(q,q')/|A|$, so that the next letter and automaton state are drawn together; the agent observes only the letter, and the proposition $\mathit{final}$ labels the states whose automaton state is accepting. After the initial observation $a_0$ and subsequent observed letters $w$, the agent's belief that it is in a $\mathit{final}$ state is $M_w(\Delta_0)(F)$; the fixed initial letter triggers no matrix update, so the automaton is non-empty iff the system satisfies $\exists\Diamond\,\mathtt B_1^{\ge\epsilon}\mathit{final}$ (respectively $\mathtt B_1^{>\epsilon}$) (Appendix A). Theorem 4 uses a separate construction with two copies of the states and an additional proposition $\mathit{found}$. A good expansion also links pages for the definitions of autonomous stochastic multiagent systems and of the semantics of PRTL* (Definitions 10, 12, 15–18 and 22, Assumptions 2 and 4), which the statement uses and which are only summarized here.

## Sources

- X. Huang, M. Kwiatkowska and M. Olejnik, "Reasoning about cognitive trust in stochastic multiagent systems", *ACM Transactions on Computational Logic* 20(4), pp. 1–64, 2019, doi:[10.1145/3329123](https://doi.org/10.1145/3329123); read in arXiv:1905.06627v1 ([arXiv](https://arxiv.org/abs/1905.06627v1)): Definition 12 (autonomous stochastic multiagent systems), Assumptions 2 and 4, Section 9 (pro-attitude synthesis, the language $\mathcal L_A(\mathrm{PRTL}^*)$ and Definition 22), Theorem 12 (the initial distribution), the syntax of PRTL* in Section 8 (Reasoning about Beliefs and Trust), Theorems 4 and 5 in Section 10 (Model Checking Complexity), their proofs in Appendix A (Undecidability of the General Problem), and Section 11 (Decidable Fragments).
