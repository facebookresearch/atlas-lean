# Alweiss–Lovett–Wu–Zhang sunflower bound

There is an absolute real constant $C$, the [sunflower constant](c.md), such that the following
holds. Let $r \ge 3$ and $w \ge 2$ be natural numbers, let $X$ be a finite set, and let
$\mathcal{F}$ be a $w$-set system of subsets of $X$, that is, every member of $\mathcal{F}$ has at
most $w$ elements. If $\mathcal{F}$ has at least

$$\left(C\, r^3 \log_{1.9} w \, \log_{1.9}(\log_{1.9} w)\right)^w$$

members, then some subfamily $S \subseteq \mathcal{F}$ is an $r$-sunflower: $S$ has exactly $r$
members and any two distinct members of $S$ intersect in $\bigcap S$.

This is Theorem 1.4 of the paper, with logarithms to base $1.9$ as there; the hypothesis $w \ge 2$
reflects the paper's assumption $\log \log w > 0$.

## Sources

- Ryan Alweiss, Shachar Lovett, Kewen Wu, and Jiapeng Zhang, *Improved bounds for the sunflower lemma*, Annals of Math. 194 (3), 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge. Problem `annals_improved_bounds_sunflower_lemma` of the lean-eval benchmark.
