# h+ is admissible and dominates h_max

For a STRIPS task in positive normal form with nonnegative operator costs, let $h^*(s)$ be the cost of an
optimal plan from $s$, $h^+(s)$ the cost of an optimal plan of the delete relaxation from $s$, and
$h_{\max}(s)$ the max-heuristic, each taking the value $\infty$ when no plan exists. Then
$h_{\max}(s) \le h^+(s) \le h^*(s)$ for every state $s$. In particular $h^+(s) = \infty$ exactly when the
goal is not relaxed reachable from $s$, and then $h^*(s) = \infty$.

## Depends on

- [Delete relaxation](delete-relaxation.md)
- [h_max and h_add](h-max-and-h-add.md)

## Proof depends on

- [Relaxed solvability is polynomial and necessary](relaxed-solvability-is-polynomial-and-necessary.md)

## Sources

- M. Helmert and C. Domshlak, *Landmarks, critical paths and abstractions: what's the difference anyway?*, ICAPS 2009, Preliminaries: the idealized heuristic $h^+$ (Hoffmann and Nebel 2001), its admissibility, and $h_{\max}$ as an admissible estimate dominated by $h^+$. <https://ai.dmi.unibas.ch/_files/teaching/hs19/po/misc/helmert-domshlak-icaps2009.pdf>
