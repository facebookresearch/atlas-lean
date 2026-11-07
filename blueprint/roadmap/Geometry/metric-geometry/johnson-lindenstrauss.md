# Johnson–Lindenstrauss lemma

There is a constant $C > 0$ with the following property. Let
$\varepsilon > 0$, let $m$ and $N \ge 2$ be natural numbers, let $X$ be a set of exactly $N$
points of $\mathbb{R}^m$ with the Euclidean norm, and let $d$ be a natural number with
$d > C \varepsilon^{-2} \log N$. Then there is a map $f : \mathbb{R}^m \to \mathbb{R}^d$ such
that $(1 - \varepsilon) \|x - y\| \le \|f(x) - f(y)\| \le (1 + \varepsilon) \|x - y\|$ for all
$x, y \in X$, where $\mathbb{R}^d$ also carries the Euclidean norm.

The map $f$ is not required to be linear, and $\varepsilon \ge 1$ is allowed (there the zero
map works). The proof takes $C = 64$ and uses a Gaussian random projection with a union bound
over pairs of points.

## Sources

- W. B. Johnson and J. Lindenstrauss, "Extensions of Lipschitz mappings into a Hilbert space," Contemporary Mathematics 26, Conference on Modern Analysis and Probability, American Mathematical Society (1984), 189--206, DOI 10.1090/conm/026/737400. ATLAS source-to-API map, item N147, module `Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/JohnsonLindenstrauss.lean`, source lines 19--140, pinned commit `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`; ATLAS adds the hypothesis that N is at least 2, and its proof rests on the placeholder `jl_probabilistic_existence`, which this proof replaces.
