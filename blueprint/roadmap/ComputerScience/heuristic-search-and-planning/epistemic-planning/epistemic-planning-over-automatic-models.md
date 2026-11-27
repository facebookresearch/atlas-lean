# Epistemic planning over automatic S5 models is undecidable with one public action

When the initial state may be an infinite S5 model given by an automatic presentation, epistemic planning is undecidable with two agents, two propositions, a single fixed public action and a fixed goal; with finite states public actions give decidability.

**Theorem.** With $Ag = \{a, b\}$, there are a public action $F$ and a formula $\varphi$ of the form $\hat{C}_{Ag}\, \psi$ such that the following restriction of the [epistemic planning problem](epistemic-planning-problem.md) is undecidable. Input: an automatic presentation of a two-agent S5 state $S$ over two propositions. Question: is there $m \ge 0$ such that $S \otimes F \otimes \cdots \otimes F$ ($m$ times) satisfies $\varphi$?

## Depends on

- [The epistemic planning problem](epistemic-planning-problem.md)

## Proof depends on

- [Rule 110 is computationally universal](../../../TheoryOfComputation/equivalence-of-models/cellular-automata/rule-110-is-computationally-universal.md)

## Expansion

From Cook's universality construction, given finite words $\alpha, \beta, \gamma$ with $|\alpha|, |\gamma| \ge 1$ it is undecidable whether the rule 110 cellular automaton evolves the configuration $\alpha^\omega \beta \gamma^\omega$ into one containing the word $01101001101000$. Such a configuration is encoded as an infinite linear state on $\mathbb{Z}$: worlds are integers linked alternately by $R_a$ and $R_b$, a proposition $\heartsuit$ marks the even positions and a proposition $p$ carries the cell values; it has an automatic presentation computable from $(\alpha, \beta, \gamma)$. A single public action $F_{R110}$ applies the local rule at every world, and the goal searches for the pattern with $\hat{C}_{Ag}$. Two further public shift actions remove the common knowledge operator from the goal (the source's Corollary 4).

## Sources

- Sébastien Lê Cong, Sophie Pinchinat and François Schwarzentruber, "Small undecidable problems in epistemic planning", *Proceedings of the Twenty-Seventh International Joint Conference on Artificial Intelligence (IJCAI 2018)*, 4780–4786, 2018, <https://doi.org/10.24963/ijcai.2018/664>; read as the open-access proceedings version, <https://www.ijcai.org/proceedings/2018/0664.pdf>: Theorems 3 and 4 and Corollary 2 in Section 4, and Corollary 4 in Section 5.
- Filippos Kominis and Hector Geffner, "Beliefs in multiagent planning: from one agent to many", *Proceedings of the Twenty-Fifth International Conference on Automated Planning and Scheduling (ICAPS 2015)*, 147–155, 2015, <https://doi.org/10.1609/icaps.v25i1.13726>: decidability of planning with public actions over finite states, as recalled in Section 1 of the IJCAI paper above.
