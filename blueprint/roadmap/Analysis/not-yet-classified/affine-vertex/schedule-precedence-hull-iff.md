# Schedule precedence over a scenario hull

Let $s$ be a finite set of scenario vectors $x \in \mathbb{R}^\iota$ ($\iota$ finite), let each activity $j$ have start time $S_j$ and affine duration $d_j(x) = a_j + \sum_i b_{j,i} x_i$, and let $E$ be a finite set of precedence pairs $(i, j)$. Then $S_i + d_i(x) \le S_j$ holds for every $(i, j) \in E$ and every $x$ in the convex hull of $s$ if and only if it holds for every $(i, j) \in E$ and every $x \in s$.
