# Sig score of a composite motif

**Setting.** For a set $S$ of regulatory sequences, a non-degenerate motif $m$ (an exact word) has an occurrence count $X_m$ whose distribution under the genomic background is modelled as Poisson with mean $\lambda_m$ (the expected count). A degenerate or **composite** motif is a set $M = \{m_1, \dots, m_n\}$ of instantiations, with count $X_M = \sum_i X_{m_i}$. If $k_i$ occurrences of $m_i$ are observed and $k = \sum_i k_i$, the significance of $M$ is $\Pr\{M \mid S\} = \Pr\{X_M \ge k\}$ and its **Sig score** is

$$\mathrm{Sig}(M) = -\log \Pr\{M \mid S\},$$

in practice Bonferroni-corrected for the number of motifs tested.

**Lemma.** For independent random variables $X, Y$ and thresholds $k_1, k_2$,

$$\Pr\{X + Y \ge k_1 + k_2\} \ge \Pr\{X \ge k_1\}\,\Pr\{Y \ge k_2\};$$

more generally, for independent $X_1, \dots, X_n$, $\Pr\{\sum_i X_i \ge \sum_i k_i\} \ge \prod_i \Pr\{X_i \ge k_i\}$.

**Theorem.** If the instantiation counts are independent, then $\mathrm{Sig}(M) \le \sum_{i=1}^n \mathrm{Sig}(m_i)$; consequently, if $\mathrm{Sig}(M) = \sigma$ then some instantiation satisfies $\mathrm{Sig}(m_i) \ge \sigma/n$.

## Expansion

The event $\{X \ge k_1\} \cap \{Y \ge k_2\}$ is contained in $\{X + Y \ge k_1 + k_2\}$, and independence turns its probability into the product; taking $-\log$ converts the product bound into subadditivity of Sig, and the average of $n$ numbers summing to at least $\sigma$ is at least $\sigma/n$. The bound is tightest when the instantiations have similar parameters and similar counts. It supports a bounded search: to find a composite motif of significance $\sigma$ covering $n$ words, it suffices to seed from words of significance at least $\sigma/n$, which prunes the exponential space of degenerate patterns while keeping every sufficiently significant one reachable. The bound holds for any $-\log$-transformed tail probability, not only the Poisson model.

## Sources

- J. M. Carlson, A. Chakravarty, R. S. Khetani, R. H. Gross, "Bounded search for de novo identification of degenerate cis-regulatory elements", BMC Bioinformatics 7:254 (2006), Lemmas 1–2, Corollary 1, Eqs 4–5 and Theorem 1, <https://doi.org/10.1186/1471-2105-7-254>, PMCID PMC1481619.
