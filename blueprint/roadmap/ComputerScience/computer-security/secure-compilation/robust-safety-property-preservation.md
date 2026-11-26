# Robust safety property preservation

A trace property $\pi$ is a *safety property* if every trace outside it has a finite bad prefix, a [finite prefix](compilation-chains-and-robust-satisfaction.md) $m$ in the
sense of terminated and open prefixes: $\forall t \notin \pi.\ \exists m \le t.\ \forall t' \ge m.\ t' \notin \pi$. Because a terminated prefix extends only to its own trace, the
property "the program does not terminate" is a safety property, whereas with ordinary sequence prefixes it would not be. A [compilation chain](compilation-chains-and-robust-satisfaction.md) satisfies *robust safety property
preservation* (RSP) if it preserves robust satisfaction of every safety property, that is, the condition of
[robust trace property preservation](robust-trace-property-preservation.md) restricted to safety properties $\pi$.

## Depends on

- [Robust trace property preservation](robust-trace-property-preservation.md)
- [Compilation chains and robust satisfaction](compilation-chains-and-robust-satisfaction.md)

## Sources

- C. Abate, R. Blanco, D. Garg, C. Hriţcu, M. Patrignani and J. Thibault, "Journey beyond full abstraction: exploring robust property preservation for secure compilation", *32nd IEEE Computer Security Foundations Symposium (CSF 2019)*, arXiv:1807.04603v6, <https://arxiv.org/abs/1807.04603v6>: Section 2.2 (safety properties and RSP), Appendix B.1 (Example B.2, rejecting termination as a safety property) and Appendix C, Definitions C.4–C.5.
