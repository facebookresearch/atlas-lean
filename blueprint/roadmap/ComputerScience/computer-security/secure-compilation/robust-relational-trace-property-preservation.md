# Robust relational trace property preservation

In a [compilation chain](compilation-chains-and-robust-satisfaction.md), a *2-relational trace property* is a relation $R$ on pairs of traces. The chain satisfies *robust 2-relational trace
property preservation* (R2rTP) if for every $R$ and all source partial programs $P_1, P_2$: if $(t_1, t_2) \in R$ whenever $C_S[P_1] \rightsquigarrow t_1$ and $C_S[P_2] \rightsquigarrow t_2$ for a common source
context $C_S$, then $(t_1, t_2) \in R$ whenever $C_T[P_1{\downarrow}] \rightsquigarrow t_1$ and $C_T[P_2{\downarrow}] \rightsquigarrow t_2$ for a common target context $C_T$. $R$ is *2-relational safety* if every
$(t_1, t_2) \notin R$ has prefixes $m_1 \le t_1$, $m_2 \le t_2$ with $(t'_1, t'_2) \notin R$ for all $t'_1 \ge m_1$, $t'_2 \ge m_2$; *robust 2-relational safety preservation* (R2rSP) restricts R2rTP to such
$R$. The $K$-ary versions RKrTP and RKrSP relate $K$ programs.

## Depends on

- [Compilation chains and robust satisfaction](compilation-chains-and-robust-satisfaction.md)

## Sources

- C. Abate, R. Blanco, D. Garg, C. Hriţcu, M. Patrignani and J. Thibault, "Journey beyond full abstraction: exploring robust property preservation for secure compilation", *32nd IEEE Computer Security Foundations Symposium (CSF 2019)*, arXiv:1807.04603v6 (numbering of this extended version, whose appendices are not in the proceedings), <https://arxiv.org/abs/1807.04603v6>: Sections 4.2–4.3 and Appendix C.3, Definitions C.38 and C.48.
