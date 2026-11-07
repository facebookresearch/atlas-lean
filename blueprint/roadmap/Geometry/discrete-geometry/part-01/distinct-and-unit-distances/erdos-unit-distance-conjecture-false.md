# Erdős's unit distance conjecture is false

There is a real number $\delta > 0$ such that for
every natural number $N$ there are an integer $n \ge N$ and a set $P$ of exactly $n$ points in the
Euclidean plane $\mathbb{R}^2$ with at least $n^{1+\delta}$ unordered pairs of points of $P$ at
distance exactly $1$.

Because $C / \log \log n \to 0$ for every constant $C$, this contradicts Erdős's conjecture that
$n$ points in the plane determine at most $n^{1 + C / \log \log n}$ unit distances for some
constant $C$ and all large $n$.

## Sources

- OpenAI, *Planar Point Sets with Many Unit Distances*, 2026. https://cdn.openai.com/pdf/74c24085-19b0-4534-9c90-465b8e29ad73/unit-distance-proof.pdf . Original conjecture: P. Erdős, *On sets of distances of n points*, Amer. Math. Monthly 53 (1946), 248-250. k-equidistant variant: P. Erdős, K. Falconer, *Some problems in combinatorial geometry*, 1997. Via leanprover/lean-eval@38361be, problem `erdos_unit_distance_conjecture_false`.
