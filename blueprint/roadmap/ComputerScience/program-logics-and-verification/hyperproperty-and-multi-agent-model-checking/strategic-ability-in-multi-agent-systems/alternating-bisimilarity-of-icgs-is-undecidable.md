# Alternating bisimilarity of concurrent game structures with imperfect information is undecidable

For concurrent game structures in which agents have imperfect information and perfect recall, the alternating bisimulation that characterizes equivalence for ATL* under the imperfect-information semantics cannot be decided: no algorithm decides whether two given structures are bisimilar for a given coalition.

**Setting (Belardinelli, Dima, Malvone and Tiplea).** Fix a set $AP$ of atoms and a set $Ag$ of agents. A *concurrent game structure with imperfect information* (iCGS) is a tuple $\mathcal{G} = \langle Ag, S, s_0, Act, \{\sim_i\}_{i \in Ag}, d, \to, \pi \rangle$ with a nonempty set $S$ of states, an initial state $s_0 \in S$, a finite nonempty set $Act$ of actions, for each agent $i$ an equivalence relation $\sim_i$ on $S$ (indistinguishability), a protocol $d : Ag \times S \to 2^{Act} \setminus \{\emptyset\}$ with $d(i, s) = d(i, s')$ whenever $s \sim_i s'$, a transition relation $\to \subseteq S \times Act^{Ag} \times S$ such that $s$ has a successor under a joint action $\vec{a}$ exactly when $a_i \in d(i, s)$ for every $i$, and a labeling $\pi : S \to 2^{AP}$. *Histories* are finite runs $s_0 \vec{a}_0 s_1 \dots s_n$; indistinguishability extends to histories synchronously: $h \sim_i h'$ if they have equal length, their states are pointwise $\sim_i$-related and agent $i$ performed the same actions in both. For a coalition $A \subseteq Ag$, $C_A(h)$ is the class of $h$ under the transitive closure of $\bigcup_{i \in A} \sim_i$ (common knowledge neighbourhood).

A *partial strategy* for agent $i$ is a partial map $\sigma$ from histories to actions with $\sigma(h) \in d(i, \mathit{last}(h))$ and $\sigma(h) = \sigma(h')$ whenever $h \sim_i h'$; a partial strategy for $A$ is one per member, and $PStr_A(Q)$ denotes those with domain $Q$. For $h$ in the domain of $\sigma_A$, $\mathit{succ}(h, \sigma_A)$ is the set of one-step extensions $h \vec{\alpha} s$ of $h$ along joint actions $\vec{\alpha}$ extending $\sigma_A(h)$. Given two iCGS $\mathcal{G}, \mathcal{G}'$ over the same agents, an *$A$-strategy simulator* is a family of maps $ST : PStr_A(C_A(h)) \to PStr_A(C'_A(h'))$, one for each pair of histories $h$ of $\mathcal{G}$ and $h'$ of $\mathcal{G}'$, depending only on the pair of neighbourhoods $(C_A(h), C'_A(h'))$. A relation $R$ between the histories of $\mathcal{G}$ and of $\mathcal{G}'$ is a *simulation for $A$* if there is a strategy simulator $ST$ such that $h \mathrel{R} h'$ implies:

1. $\pi(\mathit{last}(h)) = \pi'(\mathit{last}(h'))$;
2. for every $i \in A$ and every $k'$ with $h' \sim'_i k'$ there is $k$ with $h \sim_i k$ and $k \mathrel{R} k'$;
3. for all $k \in C_A(h)$ and $k' \in C'_A(h')$ with $k \mathrel{R} k'$, every $\sigma_A \in PStr_A(C_A(h))$ and every $l' \in \mathit{succ}(k', ST(\sigma_A))$, there is $l \in \mathit{succ}(k, \sigma_A)$ with $l \mathrel{R} l'$.

$R$ is an *$A$-bisimulation* if both $R$ and its converse are simulations for $A$, and $\mathcal{G}$ and $\mathcal{G}'$ are *$A$-bisimilar* if some $A$-bisimulation relates their initial states. $A$-bisimilar iCGS satisfy the same ATL* formulas whose only coalition is $A$, under the objective, subjective and common-knowledge semantics with perfect recall (Theorem 1 of the copy read).

**Theorem (Belardinelli, Dima, Malvone and Tiplea).** The problem of checking whether two finite iCGS $\mathcal{G}_1$ and $\mathcal{G}_2$ (finitely many states, given explicitly) defined on the same set $Ag$ of agents are $A$-bisimilar, for some set $A \subseteq Ag$ of agents, is undecidable.

The proof gives undecidability already for finite iCGS with three agents and the coalition $A = \{1, 2\}$.

## Depends on

- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The reduction is from the complement of the halting problem for deterministic Turing machines started on the empty tape. Building on a construction of Dima and Tiplea (2011) for model checking ATL under imperfect information and perfect recall, a machine $M$ is turned into a finite three-agent iCGS in which agents $1$ and $2$ have a strategy avoiding an error state if and only if $M$ never halts on the empty tape, and that strategy is then unique. A second, fixed "simple" three-agent iCGS has a unique memoryless strategy for agents $1$ and $2$ avoiding its error state (Lemma 3 of the copy read); in both structures agent $3$ resolves nondeterminism. One then shows that the two structures are $\{1, 2\}$-bisimilar if and only if $M$ never halts on the empty tape, by exhibiting an explicit functional bisimulation with a strategy simulator when $M$ does not halt. A good expansion links pages for the undecidability of halting of deterministic Turing machines started on the empty tape (the linked page states halting for codes of partial recursive functions on given inputs) and for the Dima–Tiplea encoding of Turing machine computations into iCGS with perfect recall.

## Sources

- Francesco Belardinelli, Catalin Dima, Vadim Malvone and Ferucio Tiplea, "A Hennessy-Milner Theorem for ATL with Imperfect Information", Proceedings of the 35th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2020), pp. 181–194, 2020, <https://doi.org/10.1145/3373718.3394784>; read in arXiv:2006.15000v1, <https://arxiv.org/abs/2006.15000v1>: Definition 2 (iCGS), Definitions 3, 5 and 6 (strategies, strategy simulators, memoryful simulation and bisimulation), Theorem 1 (preservation of ATL*), Lemma 3 and Theorem 5 (main statement), numbered as in arXiv:2006.15000v1.
