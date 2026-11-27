# Unfailing completion yields a ground convergent system

Let $E_0, R_0 \vdash E_1, R_1 \vdash \cdots$ be a fair run of [unfailing completion](unfailing-completion.md) with $R_0 = \emptyset$, for a reduction ordering $\succ$ that is total on ground terms. Then

1. $E_* \cup R_*$ is equivalent to $E_0$, and
2. $E_* \cup R_*$ is ground convergent with respect to $\succ$.

**Proof idea.** Part 1 follows from the preservation of the equational theory by each step, including Deduce on semi-critical pairs. For part 2, argue as for Knuth–Bendix completion on ground proofs, with the steps oriented by $\succ$ on their ground instances: by well-founded induction on the proof ordering, every ground proof that is not a rewrite proof by $\to_{(E_* \cup R_*)_\succ}$ has an equivalent smaller one, a peak being replaced by a valley or by a step with an equation that Deduce added for a semi-critical pair, which fairness provides.

## Depends on

- [Unfailing completion](unfailing-completion.md)

## Proof depends on

- [Completion steps preserve the equational theory](completion-steps-preserve-the-equational-theory.md)
- [The proof ordering of completion is well-founded](the-proof-ordering-of-completion-is-well-founded.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.7, Theorem 4.38, p. 128, obtained there analogously to Theorem 4.37.
