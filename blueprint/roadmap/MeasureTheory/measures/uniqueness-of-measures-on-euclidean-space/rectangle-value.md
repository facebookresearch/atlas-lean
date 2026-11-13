# Rectangle value of a function

For $F : \mathbb{R}^d \to \mathbb{R}$ and arbitrary
$a, b \in \mathbb{R}^d$, the rectangle value of $F$ at $a, b$ is

$$\Delta_{a,b} F = \sum_{S \subseteq \{1, \dots, d\}} (-1)^{|S|} F(v_S),$$

where $v_S \in \mathbb{R}^d$ is the vertex with $(v_S)_i = a_i$ for $i \in S$ and $(v_S)_i = b_i$
for $i \notin S$.

Write $(a, b] = \prod_{i=1}^d (a_i, b_i]$. When $a_i \le b_i$ for every $i$ and $F$ is a
distribution function on $\mathbb{R}^d$, this signed inclusion–exclusion sum equals the mass
$\mu((a, b])$ of the associated measure $\mu$.
