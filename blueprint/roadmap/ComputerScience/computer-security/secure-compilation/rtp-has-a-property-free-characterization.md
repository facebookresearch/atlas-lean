# Robust trace property preservation has a property-free characterization

**Theorem.** A compilation chain satisfies [robust trace property preservation](robust-trace-property-preservation.md) if and only if it satisfies

$$\mathrm{RTC}:\quad \forall \mathsf P.\ \forall \mathbf C_T.\ \forall t.\ \mathbf C_T[\mathsf P{\downarrow}] \rightsquigarrow t \implies \exists \mathsf C_S.\ \mathsf C_S[\mathsf P] \rightsquigarrow t:$$

every trace that a target context can produce with a compiled program is produced by the source program with some source context, which may depend on the trace.

## Depends on

- [Robust trace property preservation](robust-trace-property-preservation.md)

## Sources

- C. Abate, R. Blanco, D. Garg, C. Hriţcu, M. Patrignani and J. Thibault, "Journey beyond full abstraction: exploring robust property preservation for secure compilation", *32nd IEEE Computer Security Foundations Symposium (CSF 2019)*, arXiv:1807.04603v6, <https://arxiv.org/abs/1807.04603v6>: Section 2.1 (RTC) and Appendix C, Definition C.2 and Theorem C.3, mechanized in Coq.
