# Speculative noninterference

A *security policy* $P$ is a finite set of registers and memory addresses, the public ones, and configurations $\sigma \sim_P \sigma'$ are indistinguishable when they agree on $P$.
A [$\mu\mathrm{ASM}$ program](a-core-assembly-language-with-observations.md) $p$ satisfies *speculative noninterference* for a prediction oracle $O$ and a policy $P$ if for all initial
configurations $\sigma \sim_P \sigma'$ with equal non-speculative traces $(\!|p|\!)(\sigma) = (\!|p|\!)(\sigma')$, the [speculative traces](speculative-semantics-with-prediction-oracles.md) are equal:
$[\![p]\!]_O(\sigma) = [\![p]\!]_O(\sigma')$. Speculative execution may leak nothing beyond what the program leaks without speculation.

## Depends on

- [Speculative semantics with prediction oracles](speculative-semantics-with-prediction-oracles.md)
- [A core assembly language with leakage observations](a-core-assembly-language-with-observations.md)

## Sources

- M. Guarnieri, B. Köpf, J. F. Morales, J. Reineke and A. Sánchez, "Spectector: Principled detection of speculative information flows", *Proceedings of the 41st IEEE Symposium on Security and Privacy (S&P 2020)*, extended version arXiv:1812.08639, <https://arxiv.org/abs/1812.08639>: Section V-A (security policies) and Section V-B, Definition 1.
