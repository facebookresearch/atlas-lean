# Janson's correlation sum Δ

For a random subset $R$ with independent elements and sets $S_1, \dots, S_k$,

$$\Delta = \sum_{(i,j) \,:\, i \neq j,\ S_i \cap S_j \neq \emptyset} \Pr[S_i \subseteq R \text{ and } S_j \subseteq R],$$

over ordered pairs. Events $A_i$, $A_j$ with disjoint $S_i$, $S_j$ depend on disjoint sets of coordinates and are independent, so $\Delta$ is the [correlation sum](../first-and-second-moment-methods/dependent-pair-sum.md) of the dependency graph "$S_i \cap S_j \neq \emptyset$".

## Sources

- Yufei Zhao (lecturer) and Andrew Lin (notes), *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes, Spring 2019, https://yufeizhao.com/pm/sp19/pmnotes.pdf, Setup 7.10.
