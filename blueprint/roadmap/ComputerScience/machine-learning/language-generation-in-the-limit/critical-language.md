# Critical languages at a step

Let $U$ be a countable set of strings and $\mathcal{C} = \{L_1, L_2, \dots\}$ a countable collection of infinite languages $L_i \subseteq U$, given by a membership oracle. An adversary picks a target $K \in \mathcal{C}$ and enumerates its elements $w_1, w_2, \dots$ (every element of $K$ eventually appears; repetitions allowed); $S_t = \{w_1, \dots, w_t\}$. Let $\mathcal{C}_n = \{L_1, \dots, L_n\}$. A language $L_n$ is **critical at step $t$** if $L_n$ is consistent with $S_t$ (that is, $S_t \subseteq L_n$) and $L_n \subseteq L_i$ for every $L_i \in \mathcal{C}_n$ that is consistent with $S_t$. At every step the consistent language of least index is critical.

## Depends on

- [Generation in the limit](generation-in-the-limit.md)

## Sources

- J. Kleinberg, S. Mullainathan, "Language Generation in the Limit", NeurIPS (2024), arXiv:2404.06757.
