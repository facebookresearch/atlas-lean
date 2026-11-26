# Distributional prefix-free set-separator codes of linear expected length

Let $U$ be a finite set and $\mu$ any distribution over pairs $(A, B)$ of disjoint subsets of $U$. There is a deterministic prefix-free set-separator code $(\mathrm{enc}, \mathrm{sep})$ on $U$ (depending on $\mu$) that separates every disjoint pair and satisfies

$$
\mathbb{E}_{(A,B)\sim\mu}\big[\,|\mathrm{enc}(A,B)|\,\big] \le 2\,\mathbb{E}_{(A,B)\sim\mu}\big[|A| + |B|\big] + 7.
$$

## Proof sketch

Fix a long list of independent uniformly random subsets $R_1, R_2, \dots$ of $U$; a given disjoint pair is separated by $R_i$ with probability $2^{-(|A|+|B|)}$. Encode $(A,B)$ by a flag bit followed by the Elias gamma code of the index of the first separating set, falling back to a flag bit and the characteristic vector of $A$ if none of the first $2^{2|U|+2}$ sets separates. The first separating index is geometric with mean $2^{|A|+|B|}$, so by Jensen's inequality its gamma code has expected length at most $2(|A|+|B|) + O(1)$, and the fallback is rare enough to cost only a constant. Averaging over the random list and $\mu$ and fixing the best list derandomizes the code for $\mu$.

## Depends on

- [Separating set and set-separator code](set-separator-code.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", 64th IEEE Symposium on Foundations of Computer Science (FOCS), 2023.
- B. Chazelle, J. Kilian, R. Rubinfeld and A. Tal, "The Bloomier Filter: An Efficient Data Structure for Static Support Lookup Tables", Proceedings of the 15th ACM-SIAM Symposium on Discrete Algorithms (SODA), 2004.
