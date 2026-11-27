# Fine balance characterization of panmixia in the stochastic encounter-mating model

**Model.** A population has $x_i$ females and $y_j$ males of type $i, j \in \{1,\dots,k\}$, with $n = \sum_i x_i = \sum_j y_j \ge 1$. Each animal $\zeta$ carries an independent simple point process of *firing times* whose law depends on its sex and type. At each firing round, every single animal that fires samples a single member of the opposite sex uniformly at random (without replacement among those firing simultaneously) and forms a temporary pair; a temporary type-$ij$ pair (type-$i$ female, type-$j$ male) becomes permanent with probability $p_{ij} > 0$, independently, and otherwise both return to the singles' pool. The process stops at the time $T$ when no singles remain. The **mating pattern** $Q(T) = (Q_{ij}(T))$ counts permanent type-$ij$ pairs; it is a $k\times k$ contingency table with row sums $x_i$ and column sums $y_j$. The species is **panmictic** if $\mathbb E[Q_{ij}(T)] = x_i y_j/n$ for all $i, j$ and every population; for $k = 2$ it is **homogamous** (resp. **heterogamous**) if $\mathbb E[Q_{11}(T)] > x_1y_1/n$ (resp. $<$) whenever $x_1x_2y_1y_2 \ne 0$.

**Theorem.**

1. (Definite mating.) If $p_{ij} = 1$ for all $i, j$, then for every realization of the firing times the terminal pair list is uniform over the $n!$ perfect matchings, so it is independent of the firing times and

$$\mathbb P(Q(T) = M) = \frac{\prod_i x_i!\ \prod_j y_j!}{n!\ \prod_{i,j} m_{ij}!}$$

for every table $M$ with the given margins (multiple hypergeometric law); in particular the species is panmictic.

2. (Poisson firing times.) Let type-$i$ females fire at rate $\alpha_i \ge 0$ and type-$j$ males at rate $\beta_j \ge 0$ (independent Poisson processes, $\alpha_i + \beta_j > 0$). The law of $Q(\cdot)$ depends only on $\pi_{ij} = p_{ij}(\alpha_i + \beta_j)$, and the species is panmictic if and only if the **Poisson fine balance** condition holds:

$$\pi_{ij} + \pi_{i'j'} = \pi_{ij'} + \pi_{i'j} \quad \text{for all } i,i',j,j',$$

equivalently $\pi_{ij} = \bar\alpha_i + \bar\beta_j$ for some $\bar\alpha_i, \bar\beta_j \ge 0$. Under fine balance $Q(T)$ is multiple hypergeometric as in item 1 and $\mathbb E[Q_{ij}(t)] = \tfrac{x_iy_j}{n}\big(1 - e^{-\pi_{ij}t}\big)$. For $k = 2$ the species is heterogamous, panmictic or homogamous according as $\pi_{11} + \pi_{22}$ is $<$, $=$ or $>$ $\pi_{12} + \pi_{21}$.

3. (Bernoulli firing times.) For independent Bernoulli firing processes on $\{1,2,\dots\}$ with success probabilities $\alpha_i, \beta_j \in [0,1]$ ($\alpha_i + \beta_j > 0$), the law of $Q(\cdot)$ depends only on $\pi_{ij} = p_{ij}(\alpha_i + \beta_j - \alpha_i\beta_j) \in (0,1]$, and the species is panmictic if and only if the **Bernoulli fine balance** condition $(1-\pi_{ij})(1-\pi_{i'j'}) = (1-\pi_{ij'})(1-\pi_{i'j})$ holds. For $k = 2$ it is heterogamous, panmictic or homogamous according as $(1-\pi_{11})(1-\pi_{22})$ is $>$, $=$ or $<$ $(1-\pi_{12})(1-\pi_{21})$.

## Depends on

- [Complete positive assortative mating with equal genotype-class contribution](../complete-positive-assortative-mating-by-genotype.md)

## Expansion

Item 1 is a strong induction on $n$: the pairs formed at the first firing round are a uniformly random partial matching of the animals that fired, and the remaining singles start a fresh instance of the model. For Poisson firing times, $Q(\cdot)$ is a multidimensional pure birth chain with rates $\pi_{ij}(x_i - m_{i\cdot})(y_j - m_{\cdot j})/(n - m_{\mathrm{tot}})$, which depend on $(p_{ij}, \alpha_i, \beta_j)$ only through $\pi_{ij}$. If $\pi_{ij} = \bar\alpha_i + \bar\beta_j$, one may replace the model by one with definite mating and firing rates $\bar\alpha_i, \bar\beta_j$ without changing the law of $Q$, and item 1 applies. Conversely, the population with $n = 2$ and one animal of each type forces $\pi_{11} + \pi_{22} = \pi_{12} + \pi_{21}$ through the first-step recursion. For $k = 2$ with $\pi_{11} + \pi_{22} < \pi_{12} + \pi_{21}$ the chain is equivalent to one with definite mating for mixed pairs only, which favors mixed pairs. The Bernoulli case is the discrete-time analogue: fine balance makes $1 - \pi_{ij}$ factor as $(1-\bar\alpha_i)(1-\bar\beta_j)$.

## Sources

- Onur Gün, Atilla Yilmaz, "The stochastic encounter-mating model", *Acta Applicandae Mathematicae* 148 (2017), 71–102, <https://doi.org/10.1007/s10440-016-0079-9>; preprint arXiv:1408.5036, <https://doi.org/10.48550/arXiv.1408.5036>. Numbering of the arXiv version: Section 1.2–1.3 (model, panmixia, homogamy), Theorem 2.3, Corollaries 2.4–2.5, Proposition 3.1, Proposition 3.4, Lemma 3.5, Theorem 3.6, Corollary 3.7, Theorem 3.9, Proposition 4.1, Corollary 4.7, Theorem 4.9.
