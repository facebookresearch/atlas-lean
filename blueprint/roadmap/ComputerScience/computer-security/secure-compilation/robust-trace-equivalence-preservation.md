# Robust trace equivalence preservation

A [compilation chain](compilation-chains-and-robust-satisfaction.md) satisfies *robust trace equivalence preservation* (RTEP) if source programs that no source context
can tell apart compile to target programs that no target context can tell apart:

$$\forall \mathsf P_1, \mathsf P_2.\ \big(\forall \mathsf C_S.\ \mathrm{Behav}(\mathsf C_S[\mathsf P_1]) = \mathrm{Behav}(\mathsf C_S[\mathsf P_2])\big) \implies \big(\forall \mathbf C_T.\ \mathrm{Behav}(\mathbf C_T[\mathsf P_1{\downarrow}]) = \mathrm{Behav}(\mathbf C_T[\mathsf P_2{\downarrow}])\big).$$

RTEP is the preservation direction of fully abstract compilation, taking equality of behaviour under all contexts as the program equivalence.

## Depends on

- [Compilation chains and robust satisfaction](compilation-chains-and-robust-satisfaction.md)

## Sources

- C. Abate, R. Blanco, D. Garg, C. Hriţcu, M. Patrignani and J. Thibault, "Journey beyond full abstraction: exploring robust property preservation for secure compilation", *32nd IEEE Computer Security Foundations Symposium (CSF 2019)*, arXiv:1807.04603v6, <https://arxiv.org/abs/1807.04603v6>: Section 5 (RTEP and its relation to full abstraction) and Appendix D, Definition D.1.
