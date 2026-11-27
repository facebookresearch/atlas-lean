# k-mer spectrum bound for semi-global edit distance

**Definitions.** For a string $s$ over a finite alphabet $\Sigma$ and $k \ge 1$, the $k$-mer spectrum $\mathrm{spectrum}_k(s) \in \mathbb Z_{\ge 0}^{\Sigma^k}$ counts the occurrences of each $k$-mer in $s$. For an integer vector $v$ let $\mathrm{pos}(v)$ be the sum of its positive entries and $\mathrm{neg}(v)$ the sum of its negative entries. For $|s| = n \ge k$, $\mathrm{pos}(\mathrm{spectrum}_k(s)) = n - k + 1$.

**Observation 1 (edit distance).** If $s_2$ has edit distance $d$ from $s_1$, then for every $k$

$$\mathrm{pos}\big(\mathrm{spectrum}_k(s_1) - \mathrm{spectrum}_k(s_2)\big) \le k d, \qquad \mathrm{neg}\big(\mathrm{spectrum}_k(s_1) - \mathrm{spectrum}_k(s_2)\big) \ge -k d.$$

**Observation 2 (substrings).** If $s_1$ is a substring of $s_2$, then $\mathrm{neg}\big(\mathrm{spectrum}_k(s_2) - \mathrm{spectrum}_k(s_1)\big) = 0$.

**Lemma (semi-global bound).** If $s_1$ has edit distance $d$ from some substring $s^*$ of $s_2$, then for every $k$

$$\mathrm{pos}\big(\mathrm{spectrum}_k(s_1) - \mathrm{spectrum}_k(s_2)\big) \le k d.$$

**Filter.** Consequently, for a query $q$, a sequence $s$ and a threshold $d$, if $\mathrm{pos}(\mathrm{spectrum}_k(q) - \mathrm{spectrum}_k(s)) > k d$ for some $k$, no semi-global alignment of $q$ into $s$ has edit distance at most $d$, and the pair can be discarded without alignment.

## Depends on

- [q-gram filtering lemma for approximate matching](../../q-gram-filtering-lemma-for-approximate-matching.md)

## Expansion

A single substitution, insertion or deletion touches at most $k$ of the $k$-mer windows of a string, so it can remove at most $k$ occurrences from the spectrum (and add at most $k$); $d$ edits remove at most $kd$, giving Observation 1. A substring's $k$-mers all occur in the superstring, so passing from $s^*$ to $s_2$ only adds counts (Observation 2). Combining, $\mathrm{spectrum}_k(s_1) - \mathrm{spectrum}_k(s_2) \le \mathrm{spectrum}_k(s_1) - \mathrm{spectrum}_k(s^*)$ entrywise, whose positive part is at most $kd$. Because the bound is monotone under taking superstrings, sums of spectra over a subtree of a binary search tree give a valid test that discards whole groups of candidate centroids at once.

## Sources

- M. Ghodsi, B. Liu, M. Pop, "DNACLUST: accurate and efficient clustering of phylogenetic marker genes", BMC Bioinformatics 12:271 (2011), Methods (k-mer filtering), Observations 1–2 and Lemma 1, <https://doi.org/10.1186/1471-2105-12-271>, PMCID PMC3213679.
