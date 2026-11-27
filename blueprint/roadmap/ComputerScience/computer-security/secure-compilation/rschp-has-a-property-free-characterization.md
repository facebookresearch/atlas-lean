# RSCHP has a property-free characterization

**Theorem.** A compilation chain satisfies [robust subset-closed hyperproperty preservation](robust-subset-closed-hyperproperty-preservation.md) if and only if for every source partial
program $P$ and target context $C_T$ there is a source context $C_S$ with $\mathrm{Behav}(C_T[P{\downarrow}]) \subseteq \mathrm{Behav}(C_S[P])$: the behaviour of a compiled program in any target context
refines the behaviour of the source program in some source context.

## Depends on

- [Robust subset-closed hyperproperty preservation](robust-subset-closed-hyperproperty-preservation.md)

## Sources

- C. Abate, R. Blanco, D. Garg, C. Hriţcu, M. Patrignani and J. Thibault, "Journey beyond full abstraction: exploring robust property preservation for secure compilation", *32nd IEEE Computer Security Foundations Symposium (CSF 2019)*, arXiv:1807.04603v6 (numbering of this extended version, whose appendices are not in the proceedings), <https://arxiv.org/abs/1807.04603v6>: Section 3.2 (RSCHC) and Appendix C.2.2, Definition C.17 and Theorem C.18 (mechanized in Coq).
