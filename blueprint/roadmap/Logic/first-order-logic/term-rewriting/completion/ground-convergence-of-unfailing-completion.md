# Unfailing completion yields a ground convergent system

Let $E_0, R_0 \vdash E_1, R_1 \vdash \cdots$ be a fair run of [unfailing completion](unfailing-completion.md) with $R_0 = \emptyset$, for a reduction ordering $\succ$ that is total on ground terms. Then

1. $E_* \cup R_*$ is equivalent to $E_0$, and
2. $E_* \cup R_*$ is ground convergent with respect to $\succ$.

## Depends on

- [Unfailing completion](unfailing-completion.md)

## Proof depends on

- [Completion steps preserve the equational theory](completion-steps-preserve-the-equational-theory.md)
- [The encompassment ordering is well-founded](encompassment-ordering-is-well-founded.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.7, Theorem 4.38, p. 128, obtained there analogously to Theorem 4.37.
