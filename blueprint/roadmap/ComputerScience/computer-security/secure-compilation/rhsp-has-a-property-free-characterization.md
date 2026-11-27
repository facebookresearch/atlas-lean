# RHSP has a property-free characterization

**Theorem.** A compilation chain satisfies [robust hypersafety preservation](robust-hypersafety-preservation.md) if and only if for every source partial program $P$, target context
$C_T$ and observation $o \le \mathrm{Behav}(C_T[P{\downarrow}])$ there is a source context $C_S$ with $o \le \mathrm{Behav}(C_S[P])$. Restricting $o$ to observations of cardinality at most $K$ (not exactly $K$: a
behaviour may have fewer than $K$ distinct prefixes) characterizes robust $K$-hypersafety preservation in the same way.

## Depends on

- [Robust hypersafety preservation](robust-hypersafety-preservation.md)

## Sources

- C. Abate, R. Blanco, D. Garg, C. Hriţcu, M. Patrignani and J. Thibault, "Journey beyond full abstraction: exploring robust property preservation for secure compilation", *32nd IEEE Computer Security Foundations Symposium (CSF 2019)*, arXiv:1807.04603v6 (numbering of this extended version, whose appendices are not in the proceedings), <https://arxiv.org/abs/1807.04603v6>: Section 3.3 (RHSC) and Appendix C.2.4–C.2.5, Definitions C.27 and C.32, Definitions C.29–C.30 (observations of at most $K$ prefixes, which the statement uses; C.32 prints an equality), Theorem C.28 (proved in Coq) and Theorem C.33 (stated as analogous to the mechanized Theorem C.34).
