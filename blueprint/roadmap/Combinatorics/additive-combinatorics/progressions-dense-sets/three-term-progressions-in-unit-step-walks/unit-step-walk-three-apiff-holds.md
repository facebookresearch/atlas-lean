# Solution of Erdős Problem 192 on three-term progressions in unit-step walks

For every
natural number $d$, every sequence $a_0, a_1, a_2, \dots$ of points of $\mathbb{R}^d$ whose steps
$a_{i+1} - a_i$ are all standard unit vectors contains a three-term arithmetic progression
(indices $i$, $j$, $k$ with $a_i \ne a_j$ and $a_i + a_k = 2 a_j$) if and only if $d \le 3$.

Points $a_i, a_j, a_k$ form a progression exactly when the step words from $i$ to $j$ and from
$j$ to $k$ are permutations of each other (an abelian square). Over at most three letters every
long enough word contains an abelian square, and Keränen's infinite abelian-square-free word over
four letters gives, for every $d \ge 4$, a walk with no three-term progression.
erdosproblems.com/192 lists the problem as solved.

## Sources

- T. F. Bloom, Erdős Problems, Problem #192, https://www.erdosproblems.com/192 (status SOLVED (LEAN)); resolution: V. Keränen, Abelian squares are avoidable on 4 letters, Automata, Languages and Programming (ICALP 1992), Lecture Notes in Comput. Sci. 623, Springer (1992), 41-52, erdosproblems.com/192: true for d ≤ 3 and false for d ≥ 4, via an infinite abelian-square-free word over 4 letters (Keränen), https://doi.org/10.1007/3-540-55719-9_62.
