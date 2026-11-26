# Strict propositional tableau expansions are finite

Every strict expansion of a [propositional tableau](propositional-semantic-tableau.md) is finite: there is no infinite sequence of tableaux, each obtained from the previous one by an expansion step, that keeps the tableau strict. Hence strict maximal tableaux can be constructed effectively.

**Proof.** Start from $\{F_1, \dots, F_n\}$. The formulas added by expansion are $\top$, $\bot$ or subformulas of the expanded formula up to one negation, so all formulas that can occur lie in a finite set; let $m$ be the number of its formulas that can be expanded. By strictness each of them is expanded at most once on a branch, and each expansion adds at most two nodes to a branch, so every branch has at most $n + 2m$ nodes. Every node has at most two children, so a strict tableau has fewer than $2^{n + 2m + 1}$ nodes, and every expansion step adds a node; hence a strict expansion stops after fewer than $2^{n + 2m + 1}$ steps.

## Depends on

- [Propositional semantic tableau](propositional-semantic-tableau.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 3.18, Theorem 3.53 with its proof and the conclusion after it, p. 97, using König's lemma (Lemma 1.9, Section 1.4, p. 9).
