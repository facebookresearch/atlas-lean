# Strong late bisimilarity is an equivalence preserved by all operators except input prefix

In the [late transition semantics](late-transition-semantics-of-the-pi-calculus.md):

1. [strong late bisimilarity](strong-late-bisimilarity.md) $\dot\sim$ is an equivalence relation;
2. if $P \mathrel{\dot\sim} Q$, then $\alpha . P \mathrel{\dot\sim} \alpha . Q$ for every free action $\alpha$, and $P + R \mathrel{\dot\sim} Q + R$, $[x = y] P \mathrel{\dot\sim} [x = y] Q$, $P \mid R \mathrel{\dot\sim} Q \mid R$ and $(w) P \mathrel{\dot\sim} (w) Q$;
3. if $P\{v/y\} \mathrel{\dot\sim} Q\{v/y\}$ for every $v \in \mathrm{fn}(P, Q, y)$, then $x(y) . P \mathrel{\dot\sim} x(y) . Q$.

Transitivity is not immediate, because the composition of two strong bisimulations need not be one. The hypothesis of part 3 cannot be weakened to $P \mathrel{\dot\sim} Q$, as [the failure of preservation by input prefix](late-bisimilarity-is-not-preserved-by-input-prefix.md) shows.

## Depends on

- [Strong late bisimilarity](strong-late-bisimilarity.md)
- [Late transition semantics of the π-calculus](late-transition-semantics-of-the-pi-calculus.md)

## Proof depends on

- [Strong late bisimilarity is preserved by renaming to a fresh name](strong-late-bisimilarity-is-preserved-by-fresh-renaming.md)
- [Strong bisimulations up to restriction are contained in strong late bisimilarity](strong-bisimulations-up-to-restriction.md)

## Sources

- R. Milner, J. Parrow and D. Walker, "A calculus of mobile processes, II", *Information and Computation* 100(1):41–77, 1992, <https://www.pure.ed.ac.uk/ws/files/16426068/A_Calculus_of_Mobile_Processes_II.pdf>, Section 3.2: Lemma 6 (bisimilarity is preserved by injective renaming with a fresh name) and Theorem 2, whose proof is in the Appendix; the proofs of parallel composition and restriction use bisimulation up to restriction.
