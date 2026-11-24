# Locality-sensitive hash families

Let $d$ be a distance on a set $X$ and $d_1 < d_2$. A distribution over functions $h$ from $X$ to a finite set is $(d_1, d_2, p_1, p_2)$-*sensitive* if for all $x, y \in X$: $d(x, y) \le d_1$ implies $\Pr[h(x) = h(y)] \ge p_1$, and $d(x, y) \ge d_2$ implies $\Pr[h(x) = h(y)] \le p_2$. For example, on the nonempty subsets of a finite universe $U$, minhashing with a uniformly random permutation of $U$ is $(d_1, d_2, 1 - d_1, 1 - d_2)$-sensitive for the Jaccard distance, for $0 \le d_1 < d_2 \le 1$.

## Sources

- J. Leskovec, A. Rajaraman and J. D. Ullman, *Mining of Massive Datasets*, 2nd ed., Cambridge University Press, 2014, Sections 3.6.1 and 3.6.2
- Original work: P. Indyk and R. Motwani, "Approximate nearest neighbors: towards removing the curse of dimensionality", *Proceedings of the 30th ACM STOC*, 1998. The statement above follows Leskovec, Rajaraman and Ullman, who credit (Section 3.11) the original works on locality-sensitive hashing to it and to Gionis, Indyk and Motwani (VLDB 1999).
