# Robust trace property preservation does not imply robust noninterference preservation

In a [compilation chain](compilation-chains-and-robust-satisfaction.md) whose events include public inputs, let $\mathrm{TINI}$ be the hyperproperty of behaviours $b$ such that any two
terminating traces of $b$ with equal public inputs have equal public events; it is 2-hypersafety. *Robust TINI preservation* (RTINIP) is
[robust hyperproperty preservation](robust-hyperproperty-preservation.md) for the single hyperproperty $\mathrm{TINI}$.

**Theorem (Abate, Blanco, Garg, Hriţcu, Patrignani and Thibault).** There is a compilation chain that satisfies [robust trace property preservation](robust-trace-property-preservation.md)
but not RTINIP. In the witness, private variables of the source program are readable by target contexts: a source context reconstructed for one execution can guess the
secret it sees, but no single source context serves two executions with different secrets.

## Depends on

- [Robust trace property preservation](robust-trace-property-preservation.md)
- [Robust hyperproperty preservation](robust-hyperproperty-preservation.md)
- [Robust hypersafety preservation](robust-hypersafety-preservation.md)

## Sources

- C. Abate, R. Blanco, D. Garg, C. Hriţcu, M. Patrignani and J. Thibault, "Journey beyond full abstraction: exploring robust property preservation for secure compilation", *32nd IEEE Computer Security Foundations Symposium (CSF 2019)*, arXiv:1807.04603v6 (numbering of this extended version, whose appendices are not in the proceedings), <https://arxiv.org/abs/1807.04603v6>: Section 3.3 (the definition of TINI and RTINIP) and Section 3.4, Theorem 3.1 with the discussion before it.
