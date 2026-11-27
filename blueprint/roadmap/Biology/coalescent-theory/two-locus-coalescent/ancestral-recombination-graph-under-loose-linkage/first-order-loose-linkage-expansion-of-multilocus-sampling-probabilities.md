# First-order loose-linkage expansion of multilocus sampling probabilities

**Setting.** Sites $S$ evolve under independent mutation chains with stationary laws $\pi_i$, Kingman coalescence and recombination: for every partition $\mathcal{A}$ of $S$, recombination splitting a line according to $\mathcal{A}$ happens at rate $\varrho\, r_{\mathcal{A}}$, with $\sum_{\mathcal{A}} r_{\mathcal{A}} = 1$ and every pair of sites separable. Let $q(\nu)$ be the stationary probability of an ordered sample with type counts $\nu$ (types may be partially specified: a type $x$ is observed on the sites $D(x) \subseteq S$), and let $\sigma(\nu)$ be the linear fragmentation map that splits every sampled sequence into its single-site marginals.

**Theorem.** As $\varrho \to \infty$,

$$
q(\nu) = q_\infty(\nu) + \varrho^{-1} q_1(\nu) + O(\varrho^{-2}),
$$

where:
1. the zeroth-order term is the product of single-site sampling probabilities, $q_\infty(\nu) = \prod_{i \in S} q(\nu^{\{i\}})$, i.e. the sample behaves as if each site had its own independent Kingman coalescent;
2. the first-order term is

$$
q_1(\nu) = \sum_{x} q_\infty\bigl(\sigma(\nu) - \sigma(\delta_x)\bigr) \sum_{\substack{D(x) \subseteq A \subseteq S\\ |A| \ge 2}} \frac{(-1)^{|A \setminus D(x)|}}{\bar r_A}\binom{\nu^{\supseteq A, D(x)}(x)}{2},
$$

the outer sum running over all (partial) types $x$, including the empty type; here $\bar r_A = \sum_{\mathcal{B} : \mathcal{B}|_A \ne \{A\}} r_{\mathcal{B}}$ is the total rate at which a line carrying the sites $A$ is fragmented, $\nu^{\supseteq A, D(x)}(x)$ counts the sampled sequences observed at all sites of $A$ that agree with $x$ on $D(x)$, and $q_\infty$ vanishes on signed measures with a negative entry.

For two sites this recovers the classical loose-linkage result of Bhaskar and Song. When every recombination event splits a sequence at a single breakpoint between adjacent sites, the genealogy is the [coalescent with recombination](../coalescent-with-recombination-ancestral-material.md).

## Expansion

When recombination is fast, every sampled sequence is shattered into single-site fragments almost immediately, and the remaining genealogy is a collection of independent single-site coalescents, which gives $q_\infty$. The first correction comes from the one event that can happen before shattering is complete: two lines that still share a block $A$ of sites coalesce while both are intact on $A$. Such a pair waits a time of order $1/(\varrho\,\bar r_A)$ before fragmenting and coalesces at rate $1$ in the meantime, so the correction is $\binom{\text{count}}{2}/\bar r_A$; Möbius inversion over subsets $A \supseteq D(x)$ converts "intact on at least $A$" into "intact on exactly $D(x)$". The proof couples the marginalized ARG with its fully fragmented counterpart and shows the two differ, to order $\varrho^{-1}$, only on this single early coalescence, using a random-walk estimate on the number of lines.

## Sources

- Frederic Alberti, "Asymptotic sampling distributions made easy: loose linkage in the ancestral recombination graph", *Electronic Journal of Probability* 29 (2024), 1–30, <https://doi.org/10.1214/24-ejp1204>. Numbering as in the preprint arXiv:2301.07394v2, <https://arxiv.org/abs/2301.07394v2>: Section 2 (expansion (1)), Theorem 2.6, Lemma 3.8, Lemmas 4.4–4.5, Lemmas 5.2–5.3.
