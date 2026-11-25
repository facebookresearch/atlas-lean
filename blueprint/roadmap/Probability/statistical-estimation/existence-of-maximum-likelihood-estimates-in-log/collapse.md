# Collapsing a three-way table to $2 \times 2 \times 2$

Let $I, J, K \in \mathbb{N}$, let $n = (n_{ijk})$ be an $I \times J \times K$ table of counts, and let $a : \{1, \dots, I\} \to \{0, 1\}$, $b : \{1, \dots, J\} \to \{0, 1\}$, $c : \{1, \dots, K\} \to \{0, 1\}$ merge the levels of each variable into two classes. The collapsed $2 \times 2 \times 2$ table has cells

$$n^{abc}_{\alpha\beta\gamma} = \sum_{i, j, k \,:\, a(i) = \alpha,\ b(j) = \beta,\ c(k) = \gamma} n_{ijk}, \qquad \alpha, \beta, \gamma \in \{0, 1\}.$$

The maps $a, b, c$ need not be surjective.
