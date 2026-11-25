# Recursion for disjoint pairs by membership of a coordinate

Let $\alpha$ be a set, $i \in \alpha$ and $\mathcal{A}, \mathcal{B}$ finite families of finite subsets of $\alpha$. Write $\mathcal{A}^- = \{S \in \mathcal{A} : i \notin S\}$ and $\mathcal{A}^+ = \{S \setminus \{i\} : S \in \mathcal{A},\ i \in S\}$, and similarly for $\mathcal{B}$. Then the [number of disjoint pairs](dpairs-count.md) splits according to which set contains $i$:

$$N(\mathcal{A}, \mathcal{B}) = N(\mathcal{A}^-, \mathcal{B}^-) + N(\mathcal{A}^+, \mathcal{B}^-) + N(\mathcal{A}^-, \mathcal{B}^+).$$
