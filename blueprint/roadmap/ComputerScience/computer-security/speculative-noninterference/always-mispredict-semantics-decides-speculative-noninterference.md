# The always-mispredict semantics characterizes speculative noninterference for all oracles

Call a program $p$ *speculatively complete* for a window $w$ if, from every initial configuration with a non-speculative run to a final configuration, every
[prediction oracle](speculative-semantics-with-prediction-oracles.md) with speculative window at most $w$, and the always-mispredict semantics for $w$, give a run to a final configuration with
empty stack (the rules alone do not guarantee this: a mispredicted path can stop with a positive remaining length where no rule applies).

**Theorem (Guarnieri, Köpf, Morales, Reineke and Sánchez).** Let $p$ be speculatively complete for the window $w$. Then $p$ satisfies [speculative noninterference](speculative-noninterference.md) for a policy $P$ and every prediction
oracle with speculative window at most $w$ if and only if for all initial configurations $\sigma \sim_P \sigma'$ with $(\!|p|\!)(\sigma) = (\!|p|\!)(\sigma')$, the
[always-mispredict traces](always-mispredict-speculative-semantics.md) agree: $\{\!|p|\!\}_w(\sigma) = \{\!|p|\!\}_w(\sigma')$.

## Depends on

- [Speculative noninterference](speculative-noninterference.md)
- [Always-mispredict speculative semantics](always-mispredict-speculative-semantics.md)

## Sources

- M. Guarnieri, B. Köpf, J. F. Morales, J. Reineke and A. Sánchez, "Spectector: Principled detection of speculative information flows", *Proceedings of the 41st IEEE Symposium on Security and Privacy (S&P 2020)*, extended version arXiv:1812.08639, <https://arxiv.org/abs/1812.08639>: Section V-C, Theorem 1, proved in Appendix H with Proposition 4, used in both directions; the theorem is restricted here to speculatively complete programs, on which the progress its argument assumes holds.
