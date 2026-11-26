# Robust hyperproperty preservation

A [compilation chain](compilation-chains-and-robust-satisfaction.md) satisfies *robust hyperproperty preservation* (RHP) if it preserves robust satisfaction of every
hyperproperty $H$, a set of sets of traces:

$$\forall H.\ \forall \mathsf P.\ \big(\forall \mathsf C_S.\ \mathrm{Behav}(\mathsf C_S[\mathsf P]) \in H\big) \implies \big(\forall \mathbf C_T.\ \mathrm{Behav}(\mathbf C_T[\mathsf P{\downarrow}]) \in H\big).$$

Hyperproperties such as noninterference relate several traces of one program, so RHP preserves, for example, robust noninterference.

## Depends on

- [Compilation chains and robust satisfaction](compilation-chains-and-robust-satisfaction.md)

## Sources

- C. Abate, R. Blanco, D. Garg, C. Hriţcu, M. Patrignani and J. Thibault, "Journey beyond full abstraction: exploring robust property preservation for secure compilation", *32nd IEEE Computer Security Foundations Symposium (CSF 2019)*, arXiv:1807.04603v6, <https://arxiv.org/abs/1807.04603v6>: Section 3.1 (RHP) and Appendix C, Definition C.12.
