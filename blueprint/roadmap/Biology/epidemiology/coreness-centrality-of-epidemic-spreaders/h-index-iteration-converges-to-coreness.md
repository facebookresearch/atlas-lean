# H-index iteration converges to coreness

**Definitions.** For a finite list of reals $(x_1, \dots, x_m)$ let $\mathcal H(x_1, \dots, x_m)$ be the largest integer $y \ge 0$ such that at least $y$ of the $x_j$ are $\ge y$. Let $G = (V, E)$ be a finite undirected simple graph (a contact network), $k_i$ the degree of node $i$, and $N(i)$ its neighbor set.

- The *$n$-order H-index* is defined by $h_i^{(0)} = k_i$ and, for $n \ge 1$,

$$h_i^{(n)} = \mathcal H\big(h_{j}^{(n-1)} : j \in N(i)\big).$$

The (ordinary) H-index of node $i$ is $h_i^{(1)}$: the largest $h$ such that $i$ has at least $h$ neighbors of degree $\ge h$.
- The *coreness* $c_i$ is the largest $k$ such that $i$ belongs to the $k$-core of $G$, the maximal induced subgraph in which every node has degree $\ge k$ (equivalently, the shell index assigned by repeatedly pruning nodes of degree $\le k$).

**Theorem.** For every node $i \in V$, the sequence $h_i^{(0)}, h_i^{(1)}, h_i^{(2)}, \dots$ is nonincreasing and converges (it is eventually constant) to the coreness:

$$\lim_{n \to \infty} h_i^{(n)} = c_i .$$

So degree, H-index and coreness are the initial, first intermediate and steady states of one local iteration, and each intermediate $h^{(n)}$ is itself a centrality.

**Epidemiological use.** For discrete-time SIR spreading with per-contact infection probability $\beta$ slightly above the epidemic threshold and recovery after one step, the spreading influence $R_i$ of node $i$ is the expected final number of removed nodes when $i$ is the sole initial infective. On empirical contact, collaboration and communication networks, the Kendall rank correlation between $R_i$ and $h_i^{(1)}$ is often higher than for degree or coreness, and low orders $h^{(n)}$ interpolate between degree and coreness.

## Expansion

*Monotonicity.* $h_i^{(1)} \le k_i = h_i^{(0)}$ because $\mathcal H$ of $k_i$ numbers is at most $k_i$. If $h_j^{(n)} \le h_j^{(n-1)}$ for all $j$, monotonicity of $\mathcal H$ in each argument gives $h_i^{(n+1)} \le h_i^{(n)}$. A nonincreasing sequence of nonnegative integers is eventually constant; call its limit $h_i^{(\infty)}$.

*Lower bound.* On any subgraph $G' \subseteq G$, indices computed in $G'$ are no larger than in $G$, and in a graph with minimum degree $k_{\min}$ every $h^{(n)} \ge k_{\min}$ by induction. Applied to the $c_i$-core (minimum degree $\ge c_i$, containing $i$), this gives $h_i^{(\infty)} \ge c_i$.

*Upper bound.* At the fixed point, $h_i^{(\infty)} = \mathcal H(h_j^{(\infty)} : j \in N(i))$, so node $i$ has at least $h_i^{(\infty)}$ neighbors $j$ with $h_j^{(\infty)} \ge h_i^{(\infty)}$, and each such $j$ again has enough such neighbors. The induced subgraph on $\{j : h_j^{(\infty)} \ge h_i^{(\infty)}\}$ therefore has minimum degree $\ge h_i^{(\infty)}$ and contains $i$, so it lies in the $h_i^{(\infty)}$-core and $c_i \ge h_i^{(\infty)}$.

## Sources

- L. Lü, T. Zhou, Q.-M. Zhang, H. E. Stanley, "The H-index of a network node and its relation to degree and coreness", *Nature Communications* 7 (2016) 10168. Results, "Mathematical relationship" (operator $\mathcal H$, Eq. (2), Theorem 1) and "Quantifying spreading influences"; Methods, "Proof of Theorem 1" and "Spreading models". <https://doi.org/10.1038/ncomms10168>. PMCID: PMC4729922.
