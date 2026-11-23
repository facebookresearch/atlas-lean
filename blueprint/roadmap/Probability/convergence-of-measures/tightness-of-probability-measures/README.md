# Tight families of probability measures

Let $\alpha$ be a space carrying a $\sigma$-algebra and a topology. A family $(\mu_i)_{i \in \iota}$ of probability measures on $\alpha$ is tight if for every $\varepsilon > 0$ there is a compact set $K \subseteq \alpha$ with $\mu_i(\alpha \setminus K) \le \varepsilon$ for every index $i$. Tightness depends only on the set $\{\mu_i : i \in \iota\}$, not on the indexing.

## Idea

Tightness says that no mass escapes to infinity, uniformly over the family. On $\mathbb{R}$ it means that for every $\varepsilon > 0$ some interval $[-M, M]$ carries mass at least $1 - \varepsilon$ under every $\mu_i$. On $\mathbb{R}$, a constant family is tight, since a single probability measure on $\mathbb{R}$ gives the intervals $[-M, M]$ mass tending to $1$. The point masses at $n \in \mathbb{N}$ are not tight: their mass drifts off to infinity, and they have no weakly convergent subsequence. Prokhorov's theorem makes this exact: on the real line (and on Polish spaces), a family of probability measures is tight if and only if every sequence in it has a subsequence converging weakly to a probability measure.

## Statements

- [Tight family of probability measures](is-tight-family.md)
- [Tightness of a family is tightness of its range](is-tight-family-iff-is-tight-measure-set.md): basic property: tightness depends only on the set of laws
- [Tightness on the real line](is-tight-family-real.md): definition of the real-line form
- [Tight families on the real line concentrate on bounded intervals](is-tight-family-real-2.md): real-line form: concentration on bounded intervals
- [Real-line tightness implies tightness](is-tight-family-2.md): real-line tightness implies tightness
- [Constant families on the real line are tight](is-tight-family-of-singleton.md): example: constant families
