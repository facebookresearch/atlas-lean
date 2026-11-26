# Strict propositional tableau expansions are finite

Every strict expansion of a [propositional tableau](propositional-semantic-tableau.md) is finite: there is no infinite sequence of tableaux, each obtained from the previous one by an expansion step, that keeps the tableau strict. Hence strict maximal tableaux can be constructed effectively.

**Proof.** The formulas added by expansion are $\top$, $\bot$ or subformulas of the expanded formula up to negation, so only finitely many formulas occur. By strictness each formula is expanded at most once on a path, so every path is finite, and a finitely branching tree whose paths are all finite is finite by König's lemma.

## Depends on

- [Propositional semantic tableau](propositional-semantic-tableau.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 3.18, Theorem 3.53 with its proof and the conclusion after it, p. 97, using König's lemma (Lemma 1.9, Section 1.4, p. 9).
