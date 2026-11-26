# The always-mispredict semantics characterizes speculative noninterference for all oracles

**Theorem (Guarnieri, Köpf, Morales, Reineke and Sánchez).** A program $p$ satisfies [speculative noninterference](speculative-noninterference.md) for a policy $P$ and every prediction
oracle with speculative window at most $w$ if and only if for all initial configurations $\sigma \sim_P \sigma'$ with $(\!|p|\!)(\sigma) = (\!|p|\!)(\sigma')$, the
[always-mispredict traces](always-mispredict-speculative-semantics.md) agree: $\{\!|p|\!\}_w(\sigma) = \{\!|p|\!\}_w(\sigma')$.

## Depends on

- [Speculative noninterference](speculative-noninterference.md)
- [Always-mispredict speculative semantics](always-mispredict-speculative-semantics.md)

## Sources

- M. Guarnieri, B. Köpf, J. F. Morales, J. Reineke and A. Sánchez, "Spectector: Principled detection of speculative information flows", *Proceedings of the 41st IEEE Symposium on Security and Privacy (S&P 2020)*, extended version arXiv:1812.08639, <https://arxiv.org/abs/1812.08639>: Section V-C, Theorem 1, proved in Appendix H with Propositions 3 and 4.
