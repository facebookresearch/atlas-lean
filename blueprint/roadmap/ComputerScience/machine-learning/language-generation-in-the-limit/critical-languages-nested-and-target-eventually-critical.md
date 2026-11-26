# The target becomes critical forever and critical languages are nested

Let $U$ be a countable set of strings and $\mathcal{C} = \{L_1, L_2, \dots\}$ a countable collection of infinite languages $L_i \subseteq U$, given by a membership oracle. An adversary picks a target $K \in \mathcal{C}$ and enumerates its elements $w_1, w_2, \dots$ (every element of $K$ eventually appears; repetitions allowed); $S_t = \{w_1, \dots, w_t\}$. Let $z$ be an index with $L_z = K$. (i) There is a step $t^+$ such that $L_z$ is critical at every step $t \ge t^+$. (ii) If $i < j$ and both $L_i$ and $L_j$ are critical at step $t$, then $L_j \subseteq L_i$; hence the critical languages at step $t$, listed by increasing index, form a decreasing chain $L_{n_1} \supseteq L_{n_2} \supseteq \cdots$.

## Proof sketch

(i) For each $i < z$ with $K \not\subseteq L_i$, some element of $K \setminus L_i$ eventually appears in the enumeration, after which $L_i$ is inconsistent forever; let $t^+$ be the maximum of these finitely many times. For $t \ge t^+$ every consistent $L_i$ with $i < z$ contains $K$, so $L_z$ is critical. (ii) $L_i \in \mathcal{C}_j$ is consistent with $S_t$, so criticality of $L_j$ gives $L_j \subseteq L_i$.

## Depends on

- [Critical languages at a step](critical-language.md)

## Sources

- J. Kleinberg, S. Mullainathan, "Language Generation in the Limit", NeurIPS (2024), arXiv:2404.06757.
