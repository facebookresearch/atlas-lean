# Lovász's theorem: the Shannon capacity of the pentagon

The cycle graph $C_5$ on five
vertices has Shannon capacity $\sqrt{5}$: writing $\alpha(C_5^{\boxtimes k})$ for the independence
number of the $k$-th strong power of $C_5$, we have $\alpha(C_5^{\boxtimes k})^{1/k} \to \sqrt{5}$
as $k \to \infty$.

## Background

- [The Shannon capacity of the pentagon is at most $\sqrt 5$](le-sqrt-five-of-tendsto.md): the upper half of this theorem, proved from Lovász's umbrella and the bound $\Theta(G) \le \vartheta(G)$.

## Sources

- Knill, *Some fundamental theorems in mathematics*, §238. Problem `shannon_capacity_pentagon` of the lean-eval benchmark.
