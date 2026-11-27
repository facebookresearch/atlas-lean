# Information-theoretic lower bounds for k-mer set representations

**Setting.** Let $S$ be a set of $n$ distinct $k$-mers over an alphabet $\Sigma$ of size $\sigma$, so $S$ is an $n$-element subset of a universe of size $\sigma^k$. A *membership* data structure answers, for any $k$-mer $x$, whether $x \in S$, without errors. A *navigational* data structure answers, for $x \in S$, which of its $2\sigma$ possible one-character extensions belong to $S$ (the neighbours of $x$ in the node-centric de Bruijn graph of $S$).

**Membership lower bound.** In the worst case over sets $S$ of size $n$, any membership data structure needs at least

$$L(n,k) = \log_2\binom{\sigma^k}{n}$$

bits, and

$$n\log_2\frac{\sigma^k}{n} \;\le\; L(n,k) \;\le\; n\log_2\frac{\sigma^k}{n} + n\log_2 e .$$

Since $0 \le \log_2(\sigma^k/n) \le k\log_2\sigma$, a set that is exponentially sparse in $k$ needs $L(n,k) = \Theta(nk)$ bits.

**Navigational lower bounds.** For $\sigma = 4$, every navigational data structure needs at least $3.24\,n$ bits in the worst case. If $S$ is *linear*, i.e. its node-centric de Bruijn graph is a single unitig, $2n$ bits are necessary.

## Proof depends on

- [Partial binomial sums are at most $(eD/r)^r$](../../../../Combinatorics/binomial-coefficients/binomial-sums/bounds-on-partial-sums-of-binomial-coefficients/sum-choose-le-exp-mul-div-pow.md)

## Expansion

There are $\binom{\sigma^k}{n}$ possible sets, and a structure that answers membership correctly must distinguish all of them, which gives $L(n,k)$; the two-sided estimate follows from $(N/n)^n \le \binom{N}{n} \le (eN/n)^n$. The membership bound is asymptotically met by a structure of Conway and Bromage. A navigational structure escapes it because it is only queried on $k$-mers known to be in $S$, so it need not separate sets that agree on all neighbourhoods. These are worst-case bounds; de Bruijn graphs of real genomes are highly connected, and practical navigational structures (BOSS, spectrum-preserving string sets) use fewer bits per $k$-mer than the worst-case bounds on such inputs.

## Sources

- R. Chikhi, J. Holub, P. Medvedev, "Data structures to represent a set of k-long DNA sequences", ACM Computing Surveys 54(1) (2022), Section 6 (space lower bounds, after Conway and Bromage 2011 and Chikhi et al. 2014), <https://doi.org/10.1145/3445967>, PMCID PMC12965495.
