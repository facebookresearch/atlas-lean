# Separating set and set-separator code

Let $U$ be a finite universe. For disjoint subsets $A, B \subseteq U$, a *separating set* is a set $S^* \subseteq U$ with $A \subseteq S^*$ and $S^* \cap B = \emptyset$. A *set-separator code* on $U$ is a pair consisting of an encoding $\mathrm{enc}$ from disjoint pairs $(A, B)$ to binary strings and a decoder $\mathrm{sep} : \{0,1\}^* \times U \to \{0,1\}$ such that, for every disjoint pair, the decoded set $\{x \in U : \mathrm{sep}(\mathrm{enc}(A,B), x) = 1\}$ is a separating set for $(A,B)$. The code is *prefix-free* if the image of $\mathrm{enc}$ is a prefix-free set of strings.

## Depends on

- [Prefix-free code](../prefix-codes/is-prefix-free.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", 64th IEEE Symposium on Foundations of Computer Science (FOCS), 2023.
- B. Chazelle, J. Kilian, R. Rubinfeld and A. Tal, "The Bloomier Filter: An Efficient Data Structure for Static Support Lookup Tables", Proceedings of the 15th ACM-SIAM Symposium on Discrete Algorithms (SODA), 2004.
