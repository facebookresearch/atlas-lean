# Upper bound on replicability local fdr under truncated configuration priors

**Setting.** In the multi-study two-groups model of [At-least-$k$-of-$m$ replicability local fdr](at-least-k-of-m-replicability-local-fdr.md), gene $i$ has z-scores $Z_{i,\cdot} \in \mathbb R^m$, configurations $h \in \mathcal H = \{0,1\}^m$ with prior $\pi(h)$, likelihoods $P(Z_{i,\cdot} \mid h)$, and replicability local fdr $\mathrm{fdr}_k(Z_{i,\cdot}) = P(|H_{i,\cdot}| < k \mid Z_{i,\cdot})$. Suppose the prior is known only on a retained set $\mathcal H' \subseteq \mathcal H$, and every excluded configuration has prior mass at most $\epsilon$: $\pi(h) \le \epsilon$ for all $h \notin \mathcal H'$.

**Theorem.** For every gene,

$$\mathrm{fdr}_k(Z_{i,\cdot}) \le \frac{\displaystyle\sum_{h \in \mathcal H',\, |h| < k} P(Z_{i,\cdot} \mid h)\,\bigl(\pi(h) - \epsilon\bigr) + \epsilon \sum_{h : |h| < k} P(Z_{i,\cdot} \mid h)}{\displaystyle\sum_{h \in \mathcal H'} P(Z_{i,\cdot} \mid h)\, \pi(h)} .$$

The first numerator sum and the denominator run over the retained configurations only, and the full sum $\sum_{|h| < k} P(Z_{i,\cdot} \mid h)$ is a lower tail of a product of per-study terms, computable by the same counting dynamic program as in the independent case. With $|\mathcal H'| = n_H$ the bound costs $O(m(n_H + k))$ per gene.

**Restricted EM.** The retained prior can be estimated by the EM iteration $\pi^{(t+1)}(h) = n^{-1} \sum_i P(H_{i,\cdot} = h \mid Z_{i,\cdot}, \pi^{(t)})$: a configuration with $\pi^{(t)}(h) = 0$ stays at zero; initialised with positive weight on every retained configuration $h \in \mathcal H'$ and zero weight outside $\mathcal H'$, EM keeps these zeros and can be used to seek a local optimum of the likelihood under the constraint $\pi(h) = 0$ for $h \notin \mathcal H'$. Growing $\mathcal H'$ one study at a time and keeping the $n_H/2$ most probable prefixes gives the retained set together with a running estimate of $\epsilon$, since extending a prefix cannot increase its probability.

## Depends on

- [At-least-$k$-of-$m$ replicability local fdr](at-least-k-of-m-replicability-local-fdr.md)

## Expansion

Split $\mathrm{fdr}_k$ into retained and excluded configurations with $|h| < k$. On excluded ones replace $\pi(h)$ by $\epsilon$, which only increases the sum, and rewrite $\sum_{h \notin \mathcal H',\, |h|<k} P(Z \mid h) = \sum_{|h|<k} P(Z \mid h) - \sum_{h \in \mathcal H',\, |h|<k} P(Z \mid h)$. This gives the numerator over $P(Z_{i,\cdot})$. The numerator is nonnegative (it equals the retained posterior mass plus $\epsilon$ times the excluded likelihoods), and $P(Z_{i,\cdot}) = \sum_h P(Z_{i,\cdot} \mid h) \pi(h) \ge \sum_{h \in \mathcal H'} P(Z_{i,\cdot} \mid h) \pi(h)$, so shrinking the denominator to the retained mass preserves the inequality. The bound is conservative: declaring genes replicated when the bound is small never understates their fdr.

## Sources

- D. Amar, R. Shamir, D. Yekutieli, "Extracting replicable associations across multiple studies: empirical Bayes algorithms for controlling the false discovery rate", *PLOS Computational Biology* 13 (2017), e1005700, <https://doi.org/10.1371/journal.pcbi.1005700>; preprint "Extracting replicable associations across multiple studies: algorithms for controlling the false discovery rate", arXiv:1609.01118 (2016), Results: "Approximating the prior using restricted EM" (lemma), "Estimation under space complexity constraints" and "A fast algorithm for an upper bound for the fdr" (theorem). <https://doi.org/10.48550/arXiv.1609.01118>
