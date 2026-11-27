# Robust hypersafety preservation

In a [compilation chain](compilation-chains-and-robust-satisfaction.md), an *observation* is a finite set $o$ of finite trace prefixes, and $o \le b$ for a behaviour $b$ when every $m \in o$ is a
prefix of some trace in $b$. A hyperproperty $H$ is *hypersafety* if every $b \notin H$ has an observation $o \le b$ such that no $b' \ge o$ lies in $H$; it is *$K$-hypersafety* if such an $o$
of cardinality at most $K$ always exists. *Robust hypersafety preservation* (RHSP) and *robust $K$-hypersafety preservation* (RKHSP) are
[robust hyperproperty preservation](robust-hyperproperty-preservation.md) restricted to hypersafety and to $K$-hypersafety properties.

## Depends on

- [Compilation chains and robust satisfaction](compilation-chains-and-robust-satisfaction.md)
- [Robust hyperproperty preservation](robust-hyperproperty-preservation.md)

## Sources

- C. Abate, R. Blanco, D. Garg, C. Hriţcu, M. Patrignani and J. Thibault, "Journey beyond full abstraction: exploring robust property preservation for secure compilation", *32nd IEEE Computer Security Foundations Symposium (CSF 2019)*, arXiv:1807.04603v6 (numbering of this extended version, whose appendices are not in the proceedings), <https://arxiv.org/abs/1807.04603v6>: Section 3.3 and Appendix C.2.4–C.2.5, Definitions C.24–C.26 and C.29–C.31.
