# Logarithmic independence bound for clique-free graphs

For each fixed integer $r\ge4$ there is $c_r>0$ such that every finite simple graph $G$ on $n$ vertices with no $r$-clique and average degree $d=2|E(G)|/n\ge2$ satisfies $\alpha(G)\ge c_r n\log(d)/d$. Here $\alpha$ is the maximum cardinality of an independent vertex set, the quotient and log are real, and at $n=0$ the source's totalized average degree is zero so the hypothesis fails.

## Depends on

- Simple-graph clique freeness, independence number, and degree from twice the edge count divided by order.

## Expansion

Separate the weighted optimizer estimate from the maximum-degree theorem. For each fixed integer $r\ge4$, find $B_r>0$ such that in every finite simple $K_r$-free graph $G$, each nonnegative maximizer $w$ of $F_G(w)=\sum_v w_v(1-\log w_v)-\sum_{\{u,v\}\in E(G)}w_uw_v$ satisfies

$$
\sum_{\{u,v,z\}\text{ a triangle of }G}w_uw_vw_z\le B_r\sum_{\{u,v\}\in E(G)}w_uw_v.
$$

Both sums run over unordered sets, and the objective uses $0\log0=0$. Next, with $D_r=3+3B_r/2$, prove $\alpha(G)\ge n\log(\Delta)/(4D_r\Delta)$ whenever every vertex degree is at most a real $\Delta\ge3$. This second estimate takes a maximum-degree cap, not the average degree. The average-degree truncation belongs to the final proof.

## Proof outline

Keep the vertices of degree at most $2d$ in the original graph. At least $n/2$ remain by the degree sum, and the induced graph is still $K_r$-free and has maximum degree at most $2d$. Apply the maximum-degree bound there, use $\log(2d)\ge\log d$, and lift the independent set to $G$. This gives $c_r=1/(16D_r)$.

## Sources

- [Comparator statement: `OAI.CliqueFreeLog.logarithmic_independence_bound`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CliqueFreeLog.lean#L11-L18)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/184.md)
- [*A logarithmic independence bound for clique-free graphs*, Theorem 1.1](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-Logarithmic-Independence-Bound-for-Clique-Free-Graphs-September-25-2026/build/sections/introduction.tex#L14-L21), and [Proposition 6.1 and the degree truncation](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-Logarithmic-Independence-Bound-for-Clique-Free-Graphs-September-25-2026/build/sections/closure.tex#L13-L27).
- [Optimizer triangle-mass estimate](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/CliqueFree/IndependentSet.lean#L20-L26); [maximum-degree estimate](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/CliqueFree/MaxDegree.lean#L69-L85); [average-degree reduction](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/CliqueFree/Main.lean#L22-L82).
