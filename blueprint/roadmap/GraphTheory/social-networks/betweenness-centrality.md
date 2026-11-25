# Betweenness centrality

For a finite simple graph, the betweenness of a vertex $v$ is $B(v) = \sum \sigma_{st}(v)/\sigma_{st}$, summed over unordered pairs $\{s, t\}$ of distinct vertices other than $v$ with $\sigma_{st} > 0$, where $\sigma_{st}$ is the number of shortest $s$–$t$ paths and $\sigma_{st}(v)$ the number passing through $v$; pairs in different components contribute $0$. Other conventions (ordered pairs, which double $B$; normalization by $\binom{n-1}{2}$) give different numbers and must be stated when used.

## Sources

- D. Easley and J. Kleinberg, *Networks, Crowds, and Markets*, Cambridge University Press, 2010, Section 3.6, betweenness of a node, <https://www.cs.cornell.edu/home/kleinber/networks-book/networks-book.pdf>
