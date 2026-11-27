# Erdős Problem 659: few distances with every four points spanning three

There is a real
constant $C$ such that for every sufficiently large natural number $n$ there is a set $P$ of $n$
points of the Euclidean plane $\mathbb{R}^2$ such that every $4$-element subset of $P$ determines
at least $3$ distinct distances and $P$ determines at most $C n / \sqrt{\log n}$ distinct
distances.

A suitable truncation of the lattice $\{(a, b\sqrt{2}) : a, b \in \mathbb{Z}\}$ has
$O(n / \sqrt{\log n})$ distinct distances (Moree and Osburn) and contains none of the six
four-point configurations that determine only two distances: five of them contain a square or an
equilateral triangle (Erdős–Fishburn, Lund–Sheffer), and the pentagon configuration is excluded by
Grayzel.

## Sources

- T. F. Bloom, Erdős Problems, Problem #659, https://www.erdosproblems.com/659 (status PROVED (LEAN)); resolution: B. Grayzel, Solution to a Problem of Erdős Concerning Distances and Points, arXiv:2601.09102 (2026); P. Moree and R. Osburn, Two-dimensional lattices with few distances, Enseign. Math. (2) 52 (2006), 361-380, abstract of arXiv:2601.09102: n-point sets taken from an m × m box of the lattice {(x, √2 y)} determine O(n / √(log n)) distinct distances (Bernays' theorem for u² + 2v²) and every 4 of their points determine at least 3 distances (Perucca's classification of the six two-distance 4-point configurations); erdosproblems.com/659 records the construction (Moree-Osburn, Lund-Sheffer) and the remaining pentagon case ruled out by Grayzel (using Gemini), 'thus giving a complete solution', https://arxiv.org/abs/2601.09102.
