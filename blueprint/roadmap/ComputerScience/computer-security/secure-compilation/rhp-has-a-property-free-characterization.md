# Robust hyperproperty preservation has a property-free characterization

**Theorem.** A compilation chain satisfies [robust hyperproperty preservation](robust-hyperproperty-preservation.md) if and only if it satisfies

$$\mathrm{RHC}:\quad \forall \mathsf P.\ \forall \mathbf C_T.\ \exists \mathsf C_S.\ \mathrm{Behav}(\mathbf C_T[\mathsf P{\downarrow}]) = \mathrm{Behav}(\mathsf C_S[\mathsf P]).$$

Unlike the characterization of robust trace property preservation, one source context must reproduce exactly the set of traces of each target context, so the
compiler cannot refine behaviour, for instance by implementing a nondeterministic scheduler deterministically.

## Depends on

- [Robust hyperproperty preservation](robust-hyperproperty-preservation.md)

## Sources

- C. Abate, R. Blanco, D. Garg, C. Hriţcu, M. Patrignani and J. Thibault, "Journey beyond full abstraction: exploring robust property preservation for secure compilation", *32nd IEEE Computer Security Foundations Symposium (CSF 2019)*, arXiv:1807.04603v6, <https://arxiv.org/abs/1807.04603v6>: Section 3.1 (RHC) and Appendix C, Definition C.13 and Theorem C.14.
