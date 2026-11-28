# Optimal (1, 2)-sensitive bucketing function

**Setting.** Fix an alphabet $\Sigma$ with $|\Sigma| > 1$ and $n \ge 1$, and let $S_n = \Sigma^n$ with the Levenshtein (edit) distance $\operatorname{edit}$. For a set $B$ of buckets, a bucketing function is a map $f : S_n \to \mathcal{P}(B)$. For integers $0 \le d_1 < d_2$, $f$ is **$(d_1, d_2)$-sensitive** if for all $s, t \in S_n$

$$\operatorname{edit}(s,t) \le d_1 \Rightarrow f(s) \cap f(t) \neq \emptyset, \qquad \operatorname{edit}(s,t) \ge d_2 \Rightarrow f(s) \cap f(t) = \emptyset.$$

Requiring $|f(s)| = 1$ for all $s$ recovers deterministic locality-sensitive hashing. Write $N^d_n(s) = \{t \in S_n : \operatorname{edit}(s,t) \le d\}$.

**Lemma 1 (packing lower bound).** If $N^{d_1}_n(s)$ contains $x$ sequences with pairwise edit distance at least $d_2$, then every $(d_1,d_2)$-sensitive $f$ has $|f(s)| \ge x$.

**Theorem 1.** Let $B = \{1, \dots, n|\Sigma|^{n-1}\}$. There is a $(1,2)$-sensitive bucketing function $f : S_n \to \mathcal{P}(B)$ with $|f(s)| = n$ for every $s \in S_n$, and every bucket contains exactly $|\Sigma|$ sequences. No $(1,2)$-sensitive bucketing function exists with fewer buckets, or with $|f(s)| < n$ for some $s$.

Moreover, the $n$ buckets of any given $s$ can be computed directly in $O(n)$ arithmetic operations, so the restriction of $f$ to any subset $X \subseteq S_n$ (for example the $n$-mers of a genome) is computable in $O(n|X|)$ time.

## Expansion

*Construction.* Order $\Sigma = \{\sigma_1 < \dots < \sigma_{|\Sigma|}\}$. Scan the sequences of $S_n$ in lexicographic order and, for each occurrence of the smallest letter $\sigma_1$ at a position $i$ of a sequence $r$, open a new bucket containing the $|\Sigma|$ sequences obtained from $r$ by substituting any letter at position $i$. Each bucket is a "substitution star" at one position, so two sequences share a bucket iff they differ by at most one substitution; since equal-length sequences at edit distance $1$ differ by exactly one substitution, this is $(1,2)$-sensitive. A sequence $s$ lies in exactly one bucket per position (the one opened by $s$ with position $i$ set to $\sigma_1$), so $|f(s)| = n$, and the number of buckets equals the number of occurrences of $\sigma_1$ in $S_n$, which is $n|\Sigma|^{n-1}$ by symmetry.

*Optimality.* The $n$ single-substitution neighbours $t_i$ of $s$ (one at each position) lie in $N^1_n(s)$ and are pairwise at edit distance $2$, so Lemma 1 gives $|f(s)| \ge n$. Each bucket may only contain sequences pairwise within distance $1$; a set of equal-length sequences pairwise at edit distance at most $1$ differ at a single common position, hence has at most $|\Sigma|$ members. Counting incidences, $|B| \cdot |\Sigma| \ge n|\Sigma|^n$.

*Direct computation.* The bucket index opened at position $i$ of $r$ equals one plus the number of $\sigma_1$ occurrences in sequences lexicographically before $r$, plus those before position $i$ in $r$; that count satisfies a recursion over prefixes that evaluates in linear time.

## Sources

- K. Chen, M. Shao, "Locality-sensitive bucketing functions for the edit distance", Algorithms for Molecular Biology 18 (2023) 7, Lemmas 1–5 and Theorem 1, <https://doi.org/10.1186/s13015-023-00234-2>, PMCID PMC10367278.
