# CTL model checking in linear time

Let $M = (S, R, P)$ be a finite Kripke structure whose transition relation $R$ is total (every state has a successor) and $f$ a CTL formula. There is an algorithm that determines, for every state $s$, whether $f$ is true in $s$, in time $O(\mathrm{length}(f) \cdot (|S| + |R|))$. It labels the states with the subformulas of $f$ they satisfy, innermost first: Boolean connectives and $\mathbf{EX}$ are immediate, $\mathbf{E}[g\, \mathbf{U}\, h]$ is labelled by a backward search from the states labelled $h$ through states labelled $g$, and $\mathbf{EG}\, g$ is labelled by restricting the structure to the states labelled $g$ and searching backward from its nontrivial strongly connected components; each subformula takes time $O(|S| + |R|)$.

## Depends on

- [CTL formulas](../computation-tree-logic/formula.md)
- [Satisfaction of CTL formulas](../computation-tree-logic/satisfies.md)

## Proof depends on

- [Finite-state CTL model checking by structural recursion](../model-checking-for-computation-tree-logic/sat.md)

## Sources

- E. M. Clarke, E. A. Emerson and A. P. Sistla, "Automatic verification of finite-state concurrent systems using temporal logic specifications", *ACM Transactions on Programming Languages and Systems* 8(2):244–263, 1986, Section 3, Theorem 3.1.
