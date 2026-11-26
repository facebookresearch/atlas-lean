# Robust trace property preservation

A [compilation chain](compilation-chains-and-robust-satisfaction.md) satisfies *robust trace property preservation* (RTP) if it preserves robust satisfaction of every
trace property:

$$\forall \pi.\ \forall \mathsf P.\ \big(\forall \mathsf C_S, t.\ \mathsf C_S[\mathsf P] \rightsquigarrow t \Rightarrow t \in \pi\big) \implies \big(\forall \mathbf C_T, t.\ \mathbf C_T[\mathsf P{\downarrow}] \rightsquigarrow t \Rightarrow t \in \pi\big),$$

where $\mathsf C_S$ ranges over source contexts and $\mathbf C_T$ over target contexts. If a source program robustly satisfies a property against all source contexts, its
compilation robustly satisfies it against all target contexts.

## Depends on

- [Compilation chains and robust satisfaction](compilation-chains-and-robust-satisfaction.md)

## Sources

- C. Abate, R. Blanco, D. Garg, C. Hriţcu, M. Patrignani and J. Thibault, "Journey beyond full abstraction: exploring robust property preservation for secure compilation", *32nd IEEE Computer Security Foundations Symposium (CSF 2019)*, arXiv:1807.04603v6, <https://arxiv.org/abs/1807.04603v6>: Section 2.1 (the criterion RTP) and Appendix C, Definition C.1.
