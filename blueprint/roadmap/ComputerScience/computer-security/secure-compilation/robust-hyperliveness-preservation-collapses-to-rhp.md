# Robust hyperliveness preservation collapses to robust hyperproperty preservation

In a [compilation chain](compilation-chains-and-robust-satisfaction.md), a hyperproperty $H$ is *hyperliveness* if every observation $o$ (a finite set of finite prefixes) has a behaviour
$b \ge o$ in $H$. *Robust hyperliveness preservation* (RHLP) is [robust hyperproperty preservation](robust-hyperproperty-preservation.md) restricted to hyperliveness properties.

**Theorem.** RHLP is equivalent to RHP.

## Depends on

- [Robust hyperproperty preservation](robust-hyperproperty-preservation.md)
- [Robust hypersafety preservation](robust-hypersafety-preservation.md)
- [Compilation chains and robust satisfaction](compilation-chains-and-robust-satisfaction.md)

## Proof depends on

- [Robust hyperproperty preservation has a property-free characterization](rhp-has-a-property-free-characterization.md)

## Sources

- C. Abate, R. Blanco, D. Garg, C. Hriţcu, M. Patrignani and J. Thibault, "Journey beyond full abstraction: exploring robust property preservation for secure compilation", *32nd IEEE Computer Security Foundations Symposium (CSF 2019)*, arXiv:1807.04603v6 (numbering of this extended version, whose appendices are not in the proceedings), <https://arxiv.org/abs/1807.04603v6>: Section 3.5 and Appendix C.2.6, Definitions C.35–C.36 and Theorem C.37 (mechanized in Coq).
