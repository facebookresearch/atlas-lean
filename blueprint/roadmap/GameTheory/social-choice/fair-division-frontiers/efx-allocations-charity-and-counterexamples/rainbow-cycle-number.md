# Rainbow cycle number

For an integer $d \ge 1$, the rainbow cycle number $R(d)$ is the largest integer $k$ for which there exists a $k$-partite directed graph $G$ with parts $V_1, \dots, V_k$, each of size at most $d$, such that

1. every vertex $v \in V_i$ has at least one incoming arc from some vertex of $V_j$, for every $j \ne i$; and
2. $G$ contains no rainbow cycle, i.e. no directed cycle that visits each part at most once.

(If such graphs exist for arbitrarily large $k$ the number would be infinite; it is a theorem that $R(d)$ is finite.)

## Sources

- B. R. Chaudhury, J. Garg, K. Mehlhorn, R. Mehta, P. Misra, "Improving EFX Guarantees through Rainbow Cycle Number", EC 2021, arXiv:2103.01628.
- H. Akrami, N. Alon, B. R. Chaudhury, J. Garg, K. Mehlhorn, R. Mehta, "EFX: A Simpler Approach and an (Almost) Optimal Guarantee via Rainbow Cycle Number", EC 2023; Operations Research (2024); arXiv:2205.07638 (titled "EFX Allocations: Simplifications and Improvements").
