# Strong late equivalence

Agents $P$ and $Q$ of the [late transition semantics](late-transition-semantics-of-the-pi-calculus.md) are *strongly equivalent*, $P \sim Q$, if $P\sigma \mathrel{\dot\sim} Q\sigma$ for every substitution $\sigma$, where $\dot\sim$ is [strong late bisimilarity](strong-late-bisimilarity.md). More generally, for a symmetric irreflexive relation $D$ on names (a *distinction*), $P \sim_D Q$ if $P\sigma \mathrel{\dot\sim} Q\sigma$ for every substitution $\sigma$ that respects $D$, that is, with $x\sigma \ne y\sigma$ whenever $(x, y) \in D$; so $\sim$ is $\sim_\emptyset$.

## Depends on

- [Strong late bisimilarity](strong-late-bisimilarity.md)
- [Late transition semantics of the π-calculus](late-transition-semantics-of-the-pi-calculus.md)

## Sources

- R. Milner, J. Parrow and D. Walker, "A calculus of mobile processes, II", *Information and Computation* 100(1):41–77, 1992, <https://www.pure.ed.ac.uk/ws/files/16426068/A_Calculus_of_Mobile_Processes_II.pdf>, Section 2.2: Definitions 10, 11 and 12.
