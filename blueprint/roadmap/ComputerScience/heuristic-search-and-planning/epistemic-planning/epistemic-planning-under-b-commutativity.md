# Epistemic planning under b-commutativity

Epistemic planning over a modal logic $L$ restricts states and actions to frames validating $L$ and requires every intermediate state to stay an $L$-state; the logic $\mathrm C^b$-$\mathrm{S5}_n$ adds to multi-agent S5 the axiom that $b$ alternations $\Box_i \Box_j$ can be swapped for $\Box_j \Box_i$.

**Language and states.** Fix a finite set $\mathcal{AG}$ of $n$ agents and a set of atoms. Formulas of $\mathcal L_C$ are built from atoms by $\neg$, $\land$, $\Box_i \varphi$ ($i \in \mathcal{AG}$) and common knowledge $C_G \varphi$ ($\emptyset \ne G \subseteq \mathcal{AG}$). An *epistemic model* $M = (W, R, V)$ has a non-empty finite set of worlds, a relation $R_i$ on $W$ for each agent and a valuation; $\Box_i \varphi$ is true at $w$ if $\varphi$ is true at every $v$ with $w R_i v$, and $C_G \varphi$ if $\varphi$ is true at every $v$ reachable by $(\bigcup_{i \in G} R_i)^*$. An *epistemic state* $(M, W_d)$ has a non-empty set $W_d$ of designated worlds and satisfies $\varphi$ if every designated world does.

**Actions.** An *event model* $(E, Q, \mathit{pre}, \mathit{post})$ has a non-empty finite set of events, relations $Q_i$, preconditions $\mathit{pre}(e) \in \mathcal L_C$ and postconditions $\mathit{post}(e)(p) \in \mathcal L_C$; an *action* adds a non-empty set $E_d$ of designated events. It is *applicable* in $(M, W_d)$ if every $w \in W_d$ satisfies $\mathit{pre}(e)$ for some $e \in E_d$. The *product update* has worlds $\{(w, e) : (M, w) \models \mathit{pre}(e)\}$, relations $(w, e) R'_i (v, f)$ iff $w R_i v$ and $e Q_i f$, valuation $(w, e) \in V'(p)$ iff $(M, w) \models \mathit{post}(e)(p)$, and designated worlds $W_d \times E_d$ restricted to the new worlds.

**Logics and tasks.** All relations of states and actions are equivalence relations ($\mathrm{S5}_n$). For $b \ge 1$, $\mathrm C^b$-$\mathrm{S5}_n$ is $\mathrm{S5}_n$ plus the axiom $(\Box_i \Box_j)^b \varphi \to (\Box_j \Box_i)^b \varphi$ for all agents $i, j$. States, models and actions whose frames validate the axioms of a logic $L$ are $L$-states, $L$-models and $L$-actions. An $L$-planning task $(s_0, \mathcal A, \varphi_g)$ consists of an $L$-state, a finite set of $L$-actions and a goal $\varphi_g \in \mathcal L_C$. A *solution* is a finite sequence $\alpha_1, \dots, \alpha_m$ of actions of $\mathcal A$ such that each $\alpha_k$ is applicable in $s_0 \otimes \alpha_1 \otimes \cdots \otimes \alpha_{k-1}$, each $s_0 \otimes \alpha_1 \otimes \cdots \otimes \alpha_k$ is an $L$-state, and $s_0 \otimes \alpha_1 \otimes \cdots \otimes \alpha_m \models \varphi_g$. The *plan existence problem* $\mathrm{PlanEx}(\mathcal T_L, n)$ asks whether a given $L$-planning task with $n$ agents has a solution.

## Depends on

- [The epistemic planning problem](epistemic-planning-problem.md)
- [Epistemic models](../../../Logic/modal-logic/epistemic-logic/model.md)

## Proof depends on

None.

## Expansion

This is the general epistemic planning problem with multi-pointed states and actions, and with the extra requirement that every intermediate state validates $L$; a product update of an $L$-state with an $L$-action need not be an $L$-state, so the requirement acts as a rollback. $\mathrm C^1$ is the commutativity axiom $\Box_i \Box_j \varphi \to \Box_j \Box_i \varphi$ (whenever $i$ knows that $j$ knows $\varphi$, $j$ knows that $i$ knows it), which corresponds to the frame property that $u R_j v R_i w$ implies $u R_i x R_j w$ for some $x$. Each $\mathrm C^{b+1}$ gives a weaker logic than $\mathrm C^b$.

## Sources

- Alessandro Burigana, Paolo Felli, Marco Montali and Nicolas Troquard, "A Semantic Approach to Decidability in Epistemic Planning", in *ECAI 2023*, Frontiers in Artificial Intelligence and Applications 372, IOS Press, 2023, <https://doi.org/10.3233/FAIA230286>; read as the extended version arXiv:2307.15485v1, <https://arxiv.org/abs/2307.15485v1>: Definitions 1, 2, 5, 6, 7, 8 and 9 of Section 2 (epistemic models and states, truth, event models and actions, product update, planning tasks, solutions and the plan existence problem), and the paragraph on $b$-commutativity in Section 4.1 ("Generalizing the Principle of Commutativity"), in the numbering of that version.
