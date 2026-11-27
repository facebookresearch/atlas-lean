# Sorted prefix carries the most posterior mass

Let $\iota$ be a finite set with $m$ elements, let $\alpha : \iota \to \mathbb{R}$, and let $\sigma : \{0, \dots, m-1\} \to \iota$ be a bijection such that $i \mapsto \alpha_{\sigma(i)}$ is nonincreasing. Then for every subset $S \subseteq \iota$,

$$\sum_{j \in S} \alpha_j \le \sum_{j \in \mathrm{Pre}_\sigma(|S|)} \alpha_j,$$

where $\mathrm{Pre}_\sigma(k)$ is the [prefix](sorted-prefix.md) of length $k$: the $|S|$ largest values carry at least as much mass as any $|S|$ values.
