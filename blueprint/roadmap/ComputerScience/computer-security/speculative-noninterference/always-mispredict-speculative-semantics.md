# Always-mispredict speculative semantics

For a speculative window $w$, the *always-mispredict semantics* of a [$\mu\mathrm{ASM}$ program](a-core-assembly-language-with-observations.md) is the
[speculative semantics](speculative-semantics-with-prediction-oracles.md) changed in three ways: every branch is mispredicted, so no oracle is needed; a transaction that is not
nested gets length $w$, and a nested one the remaining length of its enclosing transaction minus $1$; and executing an instruction decrements only the innermost transaction.
After a nested transaction rolls back, the enclosing one continues as if the nested branch had been predicted correctly. $\{\!|p|\!\}_w(\sigma)$ is the trace of the run from an initial configuration $\sigma$ to a final one.

## Depends on

- [Speculative semantics with prediction oracles](speculative-semantics-with-prediction-oracles.md)
- [A core assembly language with leakage observations](a-core-assembly-language-with-observations.md)

## Sources

- M. Guarnieri, B. Köpf, J. F. Morales, J. Reineke and A. Sánchez, "Spectector: Principled detection of speculative information flows", *Proceedings of the 41st IEEE Symposium on Security and Privacy (S&P 2020)*, extended version arXiv:1812.08639, <https://arxiv.org/abs/1812.08639>: Section V-C, the three modifications, and Appendix C, Figure 10 (rules AM-NoBranch, AM-Branch, AM-Rollback).
