# Nullspace ambiguity in history matching

Take three unit-volume reservoir cells with positive concentrations $x = (x_1, x_2, x_3)$, a deterministic well map
$Gx = (x_1 + x_2, x_2 + x_3)$ and total inventory $\ell(x) = x_1 + x_2 + x_3$. The kernel of $G$ is spanned by $(1, -1, 1)$, on which
$\ell$ is not zero, so the inventory is not determined by the well data: the positive fields $(1, 1, 1)$ and $(3/2, 1/2, 3/2)$ give the
same data $(2, 2)$ but totals $3$ and $7/2$. In contrast $x_1 - x_3$, which vanishes on the kernel, is determined, as the difference of
the two observations in the noiseless model. The two displayed fields also induce identical observation laws after adding any
fixed, parameter-independent noise law, so the inventory remains statistically unidentified. The difference-of-observations
reconstruction is a noiseless identity, not an equality for each noisy sample. Nonlinear inversion is outside this result.

## Depends on

## Proof depends on

- [Observability in a linear flowsheet model](observability-in-a-linear-flowsheet-model.md)

## Sources

- J. Lebl, *Notes on Diffy Qs: Differential Equations for Engineers*, edition 6 (version 6.11), Appendix A.4.2, the kernel of a matrix, <https://www.jirka.org/diffyqs/>.
