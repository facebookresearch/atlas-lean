# Product of evaluation algebras

**Definition 3 (product operation).** Let $M$ and $N$ be evaluation algebras over the same signature $\Sigma$. Their product $M \ast\!\ast\!\ast N$ has, for each $f$ in $\Sigma$,
$$f_{M \ast\ast\ast N}((m_1, n_1), \dots, (m_k, n_k)) = \big(f_M(m_1, \dots, m_k), \ f_N(n_1, \dots, n_k)\big),$$
and the objective function
$$h_{M \ast\ast\ast N}(X) = [\, (l, r) \mid l \in L, \ r \leftarrow h_N[\, y \mid (l', y) \leftarrow X, \ l' = l \,] \,], \qquad L = h_M[\, x \mid (x, y) \leftarrow X \,],$$
where $l \in L$ ranges over $L$ as a set (duplicates ignored) and $\leftarrow$ over lists. In words: optimize the first components with $h_M$, and for each optimal first value apply $h_N$ to the second components of the candidates attaining it.

**Theorem 1.** (1) For any algebras $M$ and $N$ and answer list $x$, $(\mathrm{id}_M \ast\!\ast\!\ast \mathrm{id}_N)(x)$ is a permutation of $x$. (2) If $h_M$ and $h_N$ minimize with respect to orders $\le_M$ and $\le_N$, then $h_{M \ast\ast\ast N}$ minimizes with respect to the lexicographic order $(\le_M, \le_N)$. (3) If moreover both $M$ and $N$ satisfy Bellman's principle, so does $M \ast\!\ast\!\ast N$.

The product is evaluated by the same recurrences as each factor, so its correctness reduces to the proof obligation that $M \ast\!\ast\!\ast N$ satisfies Bellman's principle; this does not follow from the factors in general (for example the product of two counting algebras fails it). Typical uses: $\mathrm{bpmax} \ast\!\ast\!\ast \mathrm{count}$ returns the optimal number of base pairs together with the number of co-optimal structures, $\mathrm{opt} \ast\!\ast\!\ast \mathrm{pretty}$ returns all co-optimal structures, and products with classification algebras give optimal scores per structural class (shape).

## Depends on

- [Algebraic dynamic programming and Bellman's principle](algebraic-dynamic-programming-and-bellmans-principle.md)

## Expansion

Part (1) holds because the product objective with identity factors only regroups the candidates by their first component, provided $L$ is treated as a set so that nothing is duplicated. Part (2) is read off the definition: candidates are first restricted to $\le_M$-optimal first values, then optimized by $\le_N$. For part (3), Bellman's principle for a minimizing algebra is equivalent to (strict) monotonicity of the evaluation functions; componentwise monotone functions are monotone for the lexicographic order, and strictness is needed only when several optimal or the $k$ best answers are requested. The asymptotic cost of the dynamic program is unchanged when each objective returns a bounded number of answers.

## Sources

- P. Steffen, R. Giegerich, "Versatile and declarative dynamic programming using pair algebras", BMC Bioinformatics 6 (2005) 224, Definitions 1-3 and Theorem 1, <https://doi.org/10.1186/1471-2105-6-224> (PMC1261154).
