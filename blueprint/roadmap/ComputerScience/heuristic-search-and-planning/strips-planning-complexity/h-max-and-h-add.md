# h_max and h_add

This node collects the definitions of the $h_{\max}$ and $h_{\mathrm{add}}$ heuristics for STRIPS tasks in
positive normal form with nonnegative operator costs, and their properties.

## Expansion

A sound expansion has separate pages for:

1. **Definitions.** Costs take values in $[0, \infty]$. For a state $s$, the atom costs are the greatest
   solution, equivalently the limit of the iteration from $0$ on atoms of $s$ and $\infty$ elsewhere, of
   $c(p) = 0$ for $p \in s$ and $c(p) = \min_{o : p \in \mathrm{add}(o)} \bigl(\mathrm{cost}(o) + c(\mathrm{pre}(o))\bigr)$
   otherwise, where $c$ of a set is its maximum (for $h_{\max}$) or its sum (for $h_{\mathrm{add}}$), with
   $c(\emptyset) = 0$ and $\min \emptyset = \infty$. The heuristic value is $c$ of the goal; it is $\infty$
   exactly when the goal is not relaxed reachable.
2. **$h_{\max}$ is admissible and consistent** under nonnegative operator costs.
3. **$h_{\mathrm{add}}$ is in general neither**, with an explicit task as counterexample (for example, one
   operator of cost $1$ that adds two goal atoms gives $h_{\mathrm{add}} = 2 > h^* = 1$).

A good expansion adds a page for the pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: STRIPS planning as search, with admissibility and consistency of heuristics on the induced search problem.

## Depends on

- [Delete relaxation](delete-relaxation.md)

## Sources

- Foundations of AI: Automated Planning: Delete Relaxation Heuristics (slides) — University of Basel AI course (Helmert group): the cost equations for $h_{\max}$ and $h_{\mathrm{add}}$ and the slide 'h max and h add: Remarks' ($h_{\max}$ is admissible and consistent, $h_{\mathrm{add}}$ is neither). <https://ai.dmi.unibas.ch/_files/teaching/fs26/ai/slides/ai-f04-handout4.pdf>
