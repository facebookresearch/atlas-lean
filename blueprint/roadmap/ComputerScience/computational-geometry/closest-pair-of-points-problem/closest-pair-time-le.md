# Running time of the closest-pair algorithm

For every list of $n$ points in $\mathbb{R}^2$,
the closest-pair algorithm computes at most $7 n \lceil \log_2 n \rceil + n$ squared distances,
where $\lceil \log_2 0 \rceil$ is read as $0$. In particular it computes $O(n \log n)$ distances.

## Sources

- CLRS, third edition, Section 33.4.
