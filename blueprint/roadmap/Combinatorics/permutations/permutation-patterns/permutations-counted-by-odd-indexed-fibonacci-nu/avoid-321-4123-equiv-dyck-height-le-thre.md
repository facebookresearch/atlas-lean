# 321- and 4123-avoiding permutations correspond to Dyck paths of height at most three

For every natural number $n$, there is a bijection between the set $S_n(321, 4123)$ of permutations of $\{0, \dots, n-1\}$ avoiding both classical patterns $321$ and $4123$ and the set of Dyck words of semilength $n$ whose prefixes never have more than three more up steps than down steps.

A permutation $\sigma$ of $\{0, \dots, n-1\}$ contains a pattern $\pi$ of length $k$ (written with values $0, \dots, k-1$) when there are positions $e_0 < \dots < e_{k-1}$ with $\sigma(e_i) < \sigma(e_j) \iff \pi(i) < \pi(j)$ for all $i, j$; it avoids $\pi$ when it does not contain it.

## Sources

- Juan B. Gil, Felix H. Xu, and William Y. Zhu, "Odd-Indexed Fibonacci Numbers via Pattern-Avoiding Permutations", *INTEGERS* 25 (2025), Article A79, Proposition 3.
