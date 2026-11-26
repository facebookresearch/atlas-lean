# Minimum substring partitioning of reads into super-k-mers

**Definitions.** Fix integers $1\le p\le k$. For a string $x$ over $\{A,C,G,T\}$ with $|x|\ge p$, let $\min_p(x)$ be its lexicographically smallest length-$p$ substring (the *minimum $p$-substring*). For a read $s=s_1\cdots s_n$ with $n\ge k$, its $k$-mers are $s[i,i+k-1]$, $1\le i\le n-k+1$. **Minimum substring partitioning (MSP)** cuts $s$ into maximal substrings $s[i,j]$ with $j\ge i+k-1$ such that all $k$-mers of $s[i,j]$ share the same minimum $p$-substring, while this fails for $s[i,j+1]$ and $s[i-1,j]$; these are the **super-k-mers**, and each is written to the partition indexed by its shared minimum $p$-substring. With a hash $H$ and $N$ requested partitions, wrapping sends $\min_p$ to partition $H(\min_p)\bmod N$. In the canonical variant, the minimum is taken over $p$-substrings of the $k$-mer and of its reverse complement.

**Properties.**

1. *Exact partition of $k$-mer occurrences.* The super-k-mers of $s$ are $s[i_1,j_1],\dots,s[i_l,j_l]$ with $i_1=1$, $i_{m+1}=j_m-k+2$ and $j_l=n$; consecutive super-k-mers overlap in exactly $k-1$ characters, and every $k$-mer occurrence of $s$ lies in exactly one of them. Hence $\sum_{m=1}^l(j_m-i_m+2-k)=n-k+1$, and counting $k$-mers partition by partition reproduces the global $k$-mer multiset exactly.
2. *Consistency.* Equal $k$-mers, wherever they occur, have the same minimum $p$-substring and therefore land in the same partition, so per-partition hash tables never need merging. In the canonical variant a $k$-mer and its reverse complement land together, so only one orientation per pair need be stored.
3. *Compression.* A super-k-mer of length $L$ stores $L-k+1$ $k$-mers in $L$ characters instead of $k(L-k+1)$; adjacent $k$-mers share $k-1$ characters, so with $p\ll k$ runs are long, and the I/O of partitioning is roughly that of the reads themselves.
4. *Trade-off in $p$.* Smaller $p$ lengthens runs but skews partition sizes (at $p=1$ almost everything shares one partition); larger $p$ balances partitions but shortens runs (as $p\to k$ almost every $k$-mer is its own super-k-mer). Wrapping caps the $4^p$ possible partitions at $N$.

## Expansion

Property 1: along the read, the minimum $p$-substring of the sliding window is a function of the window start $i$, so the start positions split into maximal runs of constant value; a run $i,\dots,i+r-1$ is exactly the super-k-mer $s[i,i+r+k-2]$, and the next run starts at the next $k$-mer, giving the $(k-1)$-overlap. Property 2 is immediate because $\min_p$ depends only on the $k$-mer string. The minimum $p$-substring is the lexicographic minimizer of the window of $k-p+1$ consecutive $p$-mers, so MSP is minimizer-based partitioning; the sliding-window algorithm rescans a $k$-mer only when the current minimum leaves the window and otherwise compares one new $p$-substring. The k-mer counter built on MSP partitions reads to disk, then counts each partition in memory with a hash table, which makes memory use set by the largest partition rather than by the genome.

## Depends on

- [The k-mers of a string](../de-bruijn-graph-genome-assembly/kmers.md)

## Sources

- Y. Li, X. Yan, "MSPKmerCounter: A Fast and Memory Efficient Approach for K-mer Counting" (2015), Sections "Background", "Minimum Substring Partitioning" and "Methods". <https://doi.org/10.48550/arXiv.1505.06550>
