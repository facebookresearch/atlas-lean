# Robust trace property preservation does not imply robust noninterference preservation

In a [compilation chain](compilation-chains-and-robust-satisfaction.md) whose events are inputs and outputs, each classified as public or secret, let $\mathrm{TINI}$ be the
hyperproperty of behaviours $b$ such that any two terminating traces of $b$ whose sequences of public inputs agree (possibly both empty) have equal public events; it is 2-hypersafety. *Robust TINI preservation* (RTINIP) is
[robust hyperproperty preservation](robust-hyperproperty-preservation.md) for the single hyperproperty $\mathrm{TINI}$.

**Theorem (Abate, Blanco, Garg, Hriţcu, Patrignani and Thibault).** There is a compilation chain that satisfies [robust trace property preservation](robust-trace-property-preservation.md)
but not RTINIP. In the witness each run inputs one secret integer and outputs one public integer, and target contexts can read the program's private variables. Each
target trace alone is produced by a source context that returns its output as a constant, which gives RTP. But a target context can output the secret
input, producing the pair of traces $(\mathrm{input}\ 1, \mathrm{output}\ 1)$ and $(\mathrm{input}\ 2, \mathrm{output}\ 2)$, with different public outputs although their public-input
projections are the same (empty); no single source context produces both, since a source context's output is constant.

## Depends on

- [Robust trace property preservation](robust-trace-property-preservation.md)
- [Robust hyperproperty preservation](robust-hyperproperty-preservation.md)
- [Robust hypersafety preservation](robust-hypersafety-preservation.md)
- [Compilation chains and robust satisfaction](compilation-chains-and-robust-satisfaction.md)

## Proof depends on

- [Robust trace property preservation has a property-free characterization](rtp-has-a-property-free-characterization.md)

## Sources

- C. Abate, R. Blanco, D. Garg, C. Hriţcu, M. Patrignani and J. Thibault, "Journey beyond full abstraction: exploring robust property preservation for secure compilation", *32nd IEEE Computer Security Foundations Symposium (CSF 2019)*, arXiv:1807.04603v6 (numbering of this extended version, whose appendices are not in the proceedings), <https://arxiv.org/abs/1807.04603v6>: Section 3.3 (inputs and outputs classified as public or secret, and the definitions of TINI and RTINIP), Section 3.4, Theorem 3.1 with the discussion before it, and Appendix E.2, Theorem E.4 (a secret input and a public output; the per-trace source context, which establishes RTC).
