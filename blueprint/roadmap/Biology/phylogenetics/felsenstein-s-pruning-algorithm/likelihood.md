# Site likelihood of a phylogenetic tree

For a commutative semiring $R$, a finite state set $S$, leaf weights $\mathrm{obs}$, a [tree](tree.md) $t$ and a root distribution $\pi : S \to R$, the site likelihood is $\sum_{s \in S} \pi(s)\, \Lambda(t, s)$, where $\Lambda$ is the [brute-force likelihood](brute-lik.md).
