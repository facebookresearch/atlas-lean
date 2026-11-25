# Fair CTL model checking

Let $M$ be a finite Kripke structure and $F_1, \dots, F_k$ sets of states; a path is *fair* if it visits every $F_i$ infinitely often, and a state is fair if some fair path starts there. Then $s \models \mathbf{E}_f\mathbf{G}\,\varphi$ (some fair path from $s$ satisfies $\varphi$ forever) if and only if, in the subgraph of $M$ induced by the states satisfying $\varphi$, $s$ can reach a strongly connected component that contains at least one edge (a single state counts when it has a self-loop) and meets every $F_i$. Moreover $\mathbf{E}_f\mathbf{X}\,\varphi = \mathbf{E}\mathbf{X}(\varphi \wedge \mathit{fair})$ and $\mathbf{E}_f(\varphi\, \mathbf{U}\, \psi) = \mathbf{E}(\varphi\, \mathbf{U}\, (\psi \wedge \mathit{fair}))$, where $\mathit{fair} = \mathbf{E}_f\mathbf{G}\,\mathit{true}$, so fair CTL model checking takes time linear in $|M| \cdot |\varphi| \cdot \max(1, k)$.

## Proof depends on

- [Finite-state CTL model checking by structural recursion](../model-checking-for-computation-tree-logic/sat.md)

## Sources

- E. M. Clarke, O. Grumberg and D. A. Peled, *Model Checking*, MIT Press, 1999
- C. Baier and J.-P. Katoen, *Principles of Model Checking*, MIT Press, 2008, Section 6.5
- J.-P. Katoen, *Model Checking*, Lecture 14: Fairness, RWTH Aachen University, 2019, "Some useful results", "Fair path existence", "∃□a under unconditional fairness" and the complexity of fair CTL model checking, <https://moves.rwth-aachen.de/wp-content/uploads/WS1920/MC/mc2019-lecture14-slides.pdf>
