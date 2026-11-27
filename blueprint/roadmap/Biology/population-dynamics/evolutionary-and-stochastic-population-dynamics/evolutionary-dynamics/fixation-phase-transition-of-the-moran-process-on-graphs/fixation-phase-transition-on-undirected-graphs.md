# Fixation phase transition of the Moran process on undirected graphs

Let $G = (V,E)$ be a connected undirected graph on $n$ vertices. In the (birth–death) Moran process with mutant fitness $r > 0$, each vertex holds a mutant (fitness $r$) or a non-mutant (fitness $1$); at each step a vertex is chosen to reproduce with probability proportional to its fitness, and its offspring replaces a uniformly random neighbour. Start from one mutant at a uniformly random vertex and let $f_{G,r}$ be the probability that the mutants occupy all of $V$ (fixation).

**Theorem.**

1. For every $0 < r' < 1$ there is $C > 0$ such that, for every connected $n$-vertex graph with $n$ large relative to $r'$ and at most one initial mutant of fitness $r'$, the mutants go extinct with probability at least $1 - e^{-\exp(C(\log n)^{1/3})}$.
2. For every $r > 1$ there is $C > 0$ such that, for every connected $n$-vertex graph with $n$ large relative to $r$, $f_{G,r} \ge e^{C(\log n)^{1/3}}/n$.

Consequently, for all $C, r > 0$ and all sufficiently large connected undirected graphs,

$$
f_{G,r} < n^{-C} \ \text{ if } r < 1, \qquad f_{G,r} = \frac1n \ \text{ if } r = 1, \qquad f_{G,r} > \frac{(\log n)^C}{n} \ \text{ if } r > 1.
$$

## Expansion

The neutral value $1/n$ is exact by symmetry. Away from neutrality the proof uses the potential $\phi(S) = \sum_{v \in S} 1/d(v)$ and the drift $\sum_{(x,y) \in E(S, V\setminus S)} 1/(d(x)d(y))$: for $r > 1$ the expected increase of $\phi$ in one step is at least $\frac{r-1}{rn}$ times the drift. Sets with small drift ("barriers") are handled by a layered partition by degree, which yields weighted potentials whose super-martingale bounds show that a mutant that has spread into such a set fixates with overwhelming probability. The result says that every undirected graph has a sharp phase transition at $r = 1$: no undirected suppressor can drive fixation of an advantageous mutant down to order $1/n$ or below.

## Sources

- Leslie Ann Goldberg, John Lapinskas and David Richerby, *Phase Transitions of the Moran Process and Algorithmic Consequences*, arXiv:1804.02293, Theorem 2 (Section 1) and Theorems 42 and 43 (Section 4). <https://doi.org/10.48550/arXiv.1804.02293> Published version: Random Structures & Algorithms 56 (2019) 597–647, <https://doi.org/10.1002/rsa.20890>.
