# Finite collections admit uniform generation after a bounded number of distinct strings

Let $U$ be a countable set of strings and $\mathcal{C} = \{L_1, L_2, \dots\}$ a countable collection of infinite languages $L_i \subseteq U$, given by a membership oracle. An adversary picks a target $K \in \mathcal{C}$ and enumerates its elements $w_1, w_2, \dots$ (every element of $K$ eventually appears; repetitions allowed); $S_t = \{w_1, \dots, w_t\}$. If $\mathcal{C}$ is finite, there is a generator and a number $t(\mathcal{C})$ such that for every $K \in \mathcal{C}$ and every enumeration, as soon as the adversary has presented $t(\mathcal{C})$ distinct strings the generator outputs only strings of $K \setminus S_t$. The bound depends only on $\mathcal{C}$, not on the target or the enumeration.

## Proof sketch

For every subfamily $\mathcal{F} \subseteq \mathcal{C}$ whose intersection $\bigcap \mathcal{F}$ is infinite, generating from the intersection is always safe; when the intersection is finite, its size bounds how many distinct strings can be consistent with all members of $\mathcal{F}$. Let $t(\mathcal{C})$ exceed the size of every finite intersection; after that many distinct strings, the set of consistent languages has infinite intersection, and outputting an unseen element of that intersection is valid for the target.

## Depends on

- [Generation in the limit](generation-in-the-limit.md)

## Sources

- J. Kleinberg, S. Mullainathan, "Language Generation in the Limit", NeurIPS (2024), arXiv:2404.06757.
