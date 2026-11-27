# The extended pigeonhole formula $\mathrm{EPHP}^m_n$

The extended pigeonhole formula $\mathrm{EPHP}^m_n$ is a 3-CNF encoding of the pigeonhole principle: each pigeon clause $\bigvee_{j=1}^{n} p_{i,j}$ of width $n$ is replaced by a chain of clauses of width at most three through extension variables $y_{i,0},\dots,y_{i,n}$, namely $y_{i,0}$, $\neg y_{i,j-1} \vee p_{i,j} \vee y_{i,j}$ for $1 \le j \le n$, and $\neg y_{i,n}$, while the hole clauses are kept. It is satisfiable iff $\mathrm{PHP}^m_n$ is, i.e. iff $m \le n$.

## Depends on

- [Pigeonhole formulas $\mathrm{PHP}^m_n$](../resolution-lower-bounds/pigeonhole-formulas.md)

## Sources

- A. Atserias and V. Dalmau, "A Combinatorial Characterization of Resolution Width", Journal of Computer and System Sciences 74(3), 323–334, 2008: Section 5 (the formula $\mathrm{EPHP}^{n+1}_n$; variables $y_{i,j}$ there are the negations of ours).
- E. Ben-Sasson and A. Wigderson, "Short Proofs Are Narrow — Resolution Made Simple", Journal of the ACM 48(2), 149–169, 2001: Definition 4.7 and Example 4.8.
- M. Alekhnovich, E. Ben-Sasson, A. A. Razborov and A. Wigderson, "Space Complexity in Propositional Calculus", SIAM Journal on Computing 31(4), 1184–1211, 2002.
