# Nests of a symmetric form

Let $X$ be a topological space with a measure $m$ and $\mathcal E$ a [symmetric
form](symmetric-form.md) on $L^2(X; m)$. A sequence $(F_k)_{k \in \mathbb{N}}$ of subsets of $X$ is
an $\mathcal E$-nest if $F_0 \subseteq F_1 \subseteq \cdots$, every $F_k$ is closed, and
$\bigcup_k D[\mathcal E]_{F_k}$ is $\mathcal E_1$-dense in $D[\mathcal E]$: for every
$u \in D[\mathcal E]$ and $\varepsilon > 0$ there are $k$ and $v \in D[\mathcal E]_{F_k}$ with
$\mathcal E_1(u - v, u - v) < \varepsilon$. Here $D[\mathcal E]_F$ is the set of [elements of the
domain vanishing outside $F$](vanishing-outside.md) and $\mathcal E_1$ is [the form
$\mathcal E + (\cdot, \cdot)_{L^2(m)}$](energy-one.md).

## Sources

- M. Röckner and B. Schmuland, *Quasi-regular Dirichlet forms: examples and counterexamples*, Canadian Journal of Mathematics 47 (1995), 165–200, Definition 0.5(ii).
