# Hard operation distributions for dynamic dictionaries

Let $2n \le U$ and $V \ge 1$. Sample, independently, a uniformly random injective sequence of keys $k_0, \dots, k_{2n-1} \in [U]$, independent uniform values $v_0, \dots, v_{2n-1} \in [V]$, and a uniform permutation $\pi$ of $[n]$.

- The *insert–query–delete* distribution consists of the $n$ insertions $(k_i, v_i)$, $i < n$, followed by $n$ meta-operations; meta-operation $j < n$ performs $\mathrm{query}(k_{\pi(j)})$, $\mathrm{delete}(k_{\pi(j)})$ and $\mathrm{insert}(k_{n+j}, v_{n+j})$.
- The *insert–delete* distribution is the same without the queries.

Equivalently, the initial key set is a uniformly random $n$-subset of $[U]$, each deleted key is uniform among the initial keys not yet deleted, and each inserted key is uniform among the keys of $[U]$ not used before. After the initial insertions and after every meta-operation the dictionary holds exactly $n$ keys (and $n - 1$ between a deletion and the following insertion), so every operation is admissible for a dictionary of capacity $n$.

## Depends on

- [Bounded-capacity dictionary specification](../hashing/succinct-dictionaries-and-hash-families/dictionary-specifications/bounded-capacity-dictionary.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), pp. 1842-1862, 2023; arXiv:2306.02253.
