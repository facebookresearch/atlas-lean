# Robust subset-closed hyperproperty preservation

In a [compilation chain](compilation-chains-and-robust-satisfaction.md), a hyperproperty $H$ is *subset-closed* if $b_1 \subseteq b_2$ and $b_2 \in H$ imply $b_1 \in H$; the lifting
$\{b \mid b \subseteq \pi\}$ of a trace property $\pi$ is subset-closed. The chain satisfies *robust subset-closed hyperproperty preservation* (RSCHP) if for every subset-closed $H$
and every source partial program $P$: if $\mathrm{Behav}(C_S[P]) \in H$ for every source context $C_S$, then $\mathrm{Behav}(C_T[P{\downarrow}]) \in H$ for every target context $C_T$. It is
[robust hyperproperty preservation](robust-hyperproperty-preservation.md) restricted to subset-closed hyperproperties.

## Depends on

- [Compilation chains and robust satisfaction](compilation-chains-and-robust-satisfaction.md)
- [Robust hyperproperty preservation](robust-hyperproperty-preservation.md)

## Sources

- C. Abate, R. Blanco, D. Garg, C. Hriţcu, M. Patrignani and J. Thibault, "Journey beyond full abstraction: exploring robust property preservation for secure compilation", *32nd IEEE Computer Security Foundations Symposium (CSF 2019)*, arXiv:1807.04603v6 (numbering of this extended version, whose appendices are not in the proceedings), <https://arxiv.org/abs/1807.04603v6>: Section 3.2 and Appendix C.2.2, Definitions C.15 and C.16.
