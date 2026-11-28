# Generation in the limit

Let $U$ be a countable set of strings and $\mathcal{C} = \{L_1, L_2, \dots\}$ a countable collection of infinite languages $L_i \subseteq U$, given by a membership oracle. An adversary picks a target $K \in \mathcal{C}$ and enumerates its elements $w_1, w_2, \dots$ (every element of $K$ eventually appears; repetitions allowed); $S_t = \{w_1, \dots, w_t\}$. A **generator** maps each finite sequence $w_1, \dots, w_t$ to a string $g_t \in U$. It **generates from $K$ in the limit** if for every enumeration of $K$ there is $t^*$ such that $g_t \in K \setminus S_t$ for all $t \ge t^*$: from some point on, every output is a new, valid string of the target language. The collection $\mathcal{C}$ is **generatable in the limit** if one generator generates from every $K \in \mathcal{C}$ in the limit. Since all languages are infinite, valid unseen strings always exist; generating from $K$ does not require naming $K$.

## Sources

- J. Kleinberg, S. Mullainathan, "Language Generation in the Limit", NeurIPS (2024), arXiv:2404.06757.
- J. Li, V. Raman, A. Tewari, "Generation through the Lens of Learning Theory", COLT (2025), arXiv:2410.13714.
