# LM-cut heuristic

This node collects the definition of the landmark-cut heuristic for STRIPS tasks in positive normal
form with nonnegative operator costs and its bounds.

## Expansion

A sound expansion has separate pages for:

1. **Algorithm.** From a state $s$ (adding an artificial initial atom and goal operator as usual), repeat:
   compute $h_{\max}$ under the current costs; if the goal has $h_{\max} = 0$, stop; otherwise build the
   justification graph from a precondition choice function (each operator's precondition of maximal
   $h_{\max}$), let the goal zone be the atoms from which the goal is reached in that graph through operators
   of current cost $0$, and take the cut of operators leading from the atoms reachable from the initial atom
   without entering the goal zone into the goal zone; add its minimal current operator cost to the heuristic value and
   subtract that cost from every operator of the cut. If the goal is not relaxed reachable,
   $h^{\mathrm{LM\text{-}cut}}(s) = \infty$.
2. **Bounds.** $h_{\max}(s) \le h^{\mathrm{LM\text{-}cut}}(s) \le h^+(s)$, so $h^{\mathrm{LM\text{-}cut}}$ is
   admissible.
3. **Zero-cost operators** and ties in the precondition choice function, with the conventions that make
   the algorithm terminate, stated on the algorithm page.

## Depends on

- [h_max and h_add](h-max-and-h-add.md)

## Proof depends on

- [h+ is admissible and dominates h_max](h-is-admissible-and-dominates-h-max.md)

## Sources

- M. Helmert and C. Domshlak, *Landmarks, critical paths and abstractions: what's the difference anyway?*, ICAPS 2009: the landmark cut heuristic, its justification graphs, goal zone $V^*$, before-goal zone $V^0$ and cut, and its admissibility, with $h_{\max} \le h^{\mathrm{LM\text{-}cut}} \le h^+$. <https://ai.dmi.unibas.ch/_files/teaching/hs19/po/misc/helmert-domshlak-icaps2009.pdf>
