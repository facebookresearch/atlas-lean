# Hard operation distributions for dynamic dictionaries

Let $2n \le U$ and $V \ge 1$. Sample uniformly an injective sequence of keys $k_0, \dots, k_{2n-1} \in [U]$, independent uniform values $v_0, \dots, v_{2n-1} \in [V]$, and a uniform permutation $\pi$ of $[n]$.

- The *insert–query–delete* distribution consists of $n$ insertions $(k_i, v_i)$, $i < n$, followed by $n$ meta-operations; meta-operation $j$ performs $\mathrm{query}(d_j)$, $\mathrm{delete}(d_j)$ and $\mathrm{insert}(k_{n+j}, v_{n+j})$, where the deleted key $d_j$ is the key inserted in position $\pi(j)$ among the keys currently present in the order fixed by $\pi$.
- The *insert–delete* distribution is the same without the queries.

At every time the dictionary holds exactly $n$ keys, and the key set after any prefix is uniformly distributed among $n$-subsets given the observable history.

## Depends on

- [Bounded-capacity dictionary specification](../hashing/succinct-dictionaries-and-hash-families/dictionary-specifications/bounded-capacity-dictionary.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), 2023; arXiv:2306.02253.
