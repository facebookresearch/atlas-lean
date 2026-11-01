---
article_id: af_e52d230520bc874a0a117c44
declaration: def
origin: cited
statement: formalized
lean: Threshold.IsSharpThreshold
---

# Definition 4.3.14 (Sharp thresholds)

We say that $r_n$ is a sharp threshold for some property $F$ on subsets of $\Omega$ if, for every $\delta > 0$, $\mathbb{P}(\Omega_{p_n} \in F) \to 0$ when $p_n / r_n \leq 1 - \delta$, and $\mathbb{P}(\Omega_{p_n} \in F) \to 1$ when $p_n / r_n \geq 1 + \delta$. On the other hand, if there is some fixed $\varepsilon > 0$ and $0 < c < C$ so that $\mathbb{P}(\Omega_{p_n} \in F) \in [\varepsilon, 1 - \varepsilon]$ whenever $c \leq p_n / r_n \leq C$, then we say that $r_n$ is a coarse threshold.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.226 Probabilistic Methods in Combinatorics (Fall 2022), Section 4.3](../../../../../sources/v1/ProbabilisticMethodsInCombinatorics.md)
