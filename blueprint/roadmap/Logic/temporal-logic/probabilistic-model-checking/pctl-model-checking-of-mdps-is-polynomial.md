# PCTL model checking of MDPs is polynomial

Model checking a [PCTL](pctl.md) formula $\phi$ on a finite [Markov decision process](markov-decision-processes-and-adversaries.md) $M$ takes time polynomial in the size $|M|$ of the model, the total number of its nondeterministic choices, and linear in the size $|\phi|$ of the formula, the number of its connectives and temporal operators plus the sizes of its temporal operators. Each operator of $\phi$ is handled once by the [reduction to reachability](pctl-model-checking-reduces-to-reachability.md), and the most expensive case, extremal reachability probabilities, is a linear program of size $|M|$, solvable in polynomial time by the ellipsoid method. The analysis disregards the representation of numbers; if the step bounds $k$ of bounded until operators are counted in binary, the algorithm is exponential in the size of the formula.

## Depends on

- [PCTL](pctl.md)
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)
- [Markov decision processes and adversaries](markov-decision-processes-and-adversaries.md)

## Proof depends on

- [PCTL model checking reduces to reachability](pctl-model-checking-reduces-to-reachability.md)
- [Linear programs for extremal reachability probabilities](linear-programs-for-extremal-reachability-probabilities.md)
- [Linear programs are solvable in polynomial time](../../../Geometry/convex-geometry/polynomial-time-linear-programming/linear-programs-are-solvable-in-polynomial-time.md)

## Sources

- V. Forejt, M. Kwiatkowska, G. Norman and D. Parker, "Automated verification techniques for probabilistic systems", *Formal Methods for Eternal Networked Software Systems (SFM 2011)*, LNCS 6659, Springer, 2011, author copy <https://www.prismmodelchecker.org/papers/sfm11.pdf>, Section 6.4.
