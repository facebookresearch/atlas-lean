# Robust safety property preservation has a property-free characterization

**Theorem.** A compilation chain satisfies [robust safety property preservation](robust-safety-property-preservation.md) if and only if it satisfies

$$\mathrm{RSC}:\quad \forall \mathsf P.\ \forall \mathbf C_T.\ \forall m.\ \mathbf C_T[\mathsf P{\downarrow}] \rightsquigarrow m \implies \exists \mathsf C_S.\ \mathsf C_S[\mathsf P] \rightsquigarrow m,$$

the analogue of the characterization of RTP with [finite prefixes](compilation-chains-and-robust-satisfaction.md) $m$, terminated or open, in place of traces.

## Depends on

- [Robust safety property preservation](robust-safety-property-preservation.md)
- [Compilation chains and robust satisfaction](compilation-chains-and-robust-satisfaction.md)

## Sources

- C. Abate, R. Blanco, D. Garg, C. Hriţcu, M. Patrignani and J. Thibault, "Journey beyond full abstraction: exploring robust property preservation for secure compilation", *32nd IEEE Computer Security Foundations Symposium (CSF 2019)*, arXiv:1807.04603v6, <https://arxiv.org/abs/1807.04603v6>: Section 2.2 (RSC) and Appendix C, Definition C.6 and Theorem C.7, mechanized in Coq.
