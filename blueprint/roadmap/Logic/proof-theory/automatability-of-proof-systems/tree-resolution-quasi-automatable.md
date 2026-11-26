# Tree-like resolution is quasi-polynomially automatable

There is an algorithm that, given an unsatisfiable CNF $F$ on $n$ variables that has a tree-like resolution refutation of size $s$, finds a tree-like refutation in time $n^{O(\log s)}$. General resolution is automatable in time $n^{O(w_0 + \sqrt{n \log s})}$, where $w_0$ is the maximum initial clause width, by searching for refutations of increasing width.

## Proof sketch

A tree-like refutation of size $s$ has a root-adjacent subtree of size at most $s/2$ on one side of the first branching variable; recursively search both restrictions $F|_{x = 0}$ and $F|_{x = 1}$ with the size budget halved on one side, trying all variables, which gives the recurrence $T(s) \le 2n\, T(s/2) + \operatorname{poly}$ and time $n^{O(\log s)}$. For general resolution, Ben-Sasson-Wigderson bounds the minimum width by $O(\sqrt{n \log s})$, and width-$w$ refutations are found in time $n^{O(w)}$ by saturation.

## Depends on

- [Automatable proof systems](automatable-proof-system.md)
- [Ben-Sasson–Wigderson for general resolution](../../propositional-logic/resolution-size-and-width/refutation-narrow.md)
- [Ben-Sasson–Wigderson for tree-like resolution](../../propositional-logic/resolution-size-and-width/tree-refutation-narrow.md)
- [DPLL search trees and tree-like resolution simulate each other](../../propositional-logic/sat-solving/dpll-search-trees-and-tree-like-resolution.md)

## Proof depends on

- [Automatable proof systems](automatable-proof-system.md)
- [Ben-Sasson–Wigderson for general resolution](../../propositional-logic/resolution-size-and-width/refutation-narrow.md)
- [Ben-Sasson–Wigderson for tree-like resolution](../../propositional-logic/resolution-size-and-width/tree-refutation-narrow.md)
- [DPLL search trees and tree-like resolution simulate each other](../../propositional-logic/sat-solving/dpll-search-trees-and-tree-like-resolution.md)

## Sources

- P. Beame, T. Pitassi, "Simplified and improved resolution lower bounds", FOCS (1996).
- E. Ben-Sasson, A. Wigderson, "Short proofs are narrow - resolution made simple", Journal of the ACM 48 (2001) 149-169.
