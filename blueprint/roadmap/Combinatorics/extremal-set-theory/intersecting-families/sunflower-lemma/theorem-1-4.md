# Alweiss–Lovett–Wu–Zhang sunflower bound

Let $C$ be the sunflower constant, a real number
not depending on $r$ or $w$. Let $r \ge 3$ and $w \ge 2$ be natural numbers, let $X$ be a finite
type, and let $\mathcal{F}$ be a $w$-set system of subsets of $X$, that is, every member of
$\mathcal{F}$ has at most $w$ elements. If $\mathcal{F}$ has at least

$$\left(C\, r^3 \log_{1.9} w \, \log_{1.9}(\log_{1.9} w)\right)^w$$

members, then some subfamily $S \subseteq \mathcal{F}$ is an $r$-sunflower: $S$ has exactly $r$
members and any two distinct members of $S$ intersect in $\bigcap S$.

This is Theorem 1.4 (main theorem, sunflowers); logarithms are to base $1.9$, as in the paper.
We require $w \ge 2$, as the paper assumes $\log \log w > 0$.

## Sources

- R. Alweiss, S. Lovett, K. Wu, and J. Zhang, `Improved bounds for the sunflower lemma`, Annals of Math, 194 (3) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-3-ImprovedBoundsSunflowerLemma.lean Via leanprover/lean-eval@38361be, problem `annals_improved_bounds_sunflower_lemma`.
