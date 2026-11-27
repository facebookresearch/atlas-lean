# Strong late bisimilarity is preserved by renaming to a fresh name

In the [late transition semantics](late-transition-semantics-of-the-pi-calculus.md), if $P \mathrel{\dot\sim} Q$ for [strong late bisimilarity](strong-late-bisimilarity.md) and $w \notin \mathrm{fn}(P, Q)$, then $P\{w/z\} \mathrel{\dot\sim} Q\{w/z\}$ for every name $z$.

## Depends on

- [Strong late bisimilarity](strong-late-bisimilarity.md)
- [Late transition semantics of the π-calculus](late-transition-semantics-of-the-pi-calculus.md)

## Sources

- R. Milner, J. Parrow and D. Walker, "A calculus of mobile processes, II", *Information and Computation* 100(1):41–77, 1992, <https://www.pure.ed.ac.uk/ws/files/16426068/A_Calculus_of_Mobile_Processes_II.pdf>, Section 3.2: Lemma 6, with the bisimulation used in its proof; the proof is in the Appendix.
