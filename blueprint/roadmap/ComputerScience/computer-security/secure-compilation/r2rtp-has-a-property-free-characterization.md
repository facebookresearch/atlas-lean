# R2rTP has a property-free characterization

**Theorem.** A compilation chain satisfies [robust 2-relational trace property preservation](robust-relational-trace-property-preservation.md) if and only if for all source partial
programs $P_1, P_2$, every target context $C_T$ and all traces with $C_T[P_1{\downarrow}] \rightsquigarrow t_1$ and $C_T[P_2{\downarrow}] \rightsquigarrow t_2$, there is a single source context $C_S$ with
$C_S[P_1] \rightsquigarrow t_1$ and $C_S[P_2] \rightsquigarrow t_2$.

## Depends on

- [Robust relational trace property preservation](robust-relational-trace-property-preservation.md)

## Sources

- C. Abate, R. Blanco, D. Garg, C. Hriţcu, M. Patrignani and J. Thibault, "Journey beyond full abstraction: exploring robust property preservation for secure compilation", *32nd IEEE Computer Security Foundations Symposium (CSF 2019)*, arXiv:1807.04603v6 (numbering of this extended version, whose appendices are not in the proceedings), <https://arxiv.org/abs/1807.04603v6>: Section 4.2 (R2rTC) and Appendix C.3.1, Definition C.39 and Theorem C.40 (mechanized in Coq).
