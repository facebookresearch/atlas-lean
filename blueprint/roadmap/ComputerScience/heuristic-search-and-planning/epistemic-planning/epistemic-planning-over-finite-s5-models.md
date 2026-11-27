# Epistemic planning over finite S5 models is undecidable with one fixed action

Epistemic planning is undecidable for two agents and finite S5 initial states over at most six propositions, even with one fixed action as the whole repertoire and a fixed goal; only the initial state is part of the input.

**Theorem.** With $Ag = \{a, b\}$, there are an action $F$ and a formula $\varphi$ of the form $\hat{C}_{Ag}\, \psi$ such that the following restriction of the [epistemic planning problem](epistemic-planning-problem.md) is undecidable. Input: a finite S5 state $S$ over at most six propositions. Question: is there $m \ge 0$ such that $S \otimes F \otimes \cdots \otimes F$ ($m$ times) is defined and satisfies $\varphi$?

## Depends on

- [The epistemic planning problem](epistemic-planning-problem.md)

## Proof depends on

None.

## Expansion

Smith showed that every $m$-symbol $n$-state Turing machine is simulated by a one-dimensional three-neighbor cellular automaton with $m + 2n$ symbols and a blank background; applied to Minsky's 4-symbol 7-state universal machine this gives an 18-symbol universal automaton $\mathcal{A}_{Smith}$ and a finite word $h$ such that it is undecidable whether the configuration $\cdots\_\,\alpha\,\_\cdots$ (blank outside a finite word $\alpha$) evolves into one containing $h$. A finite support is encoded as a finite linear state: worlds $-n, \dots, n$ forming a chain linked alternately by $R_a$ and $R_b$, the symbol of each cell encoded in five propositions $p_1, \dots, p_5$ and a sixth proposition $\heartsuit$ marking the even worlds. One application of the fixed action $F_{Smith}$ performs one synchronous step of the automaton through its pre- and postconditions, and the goal $\hat{C}_{Ag}\, \mathit{wenc}(h)$ searches the chain for the pattern $h$. Two further fixed actions shifting the chain remove the common knowledge operator from the goal (the source's Corollary 3).

## Sources

- Sébastien Lê Cong, Sophie Pinchinat and François Schwarzentruber, "Small undecidable problems in epistemic planning", *Proceedings of the Twenty-Seventh International Joint Conference on Artificial Intelligence (IJCAI 2018)*, 4780–4786, 2018, <https://doi.org/10.24963/ijcai.2018/664>; read as the open-access proceedings version, <https://www.ijcai.org/proceedings/2018/0664.pdf>: Theorems 1 and 2 and Corollary 1 in Section 3, and Corollary 3 in Section 5.
