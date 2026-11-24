# Upper bound for a restricted exponential integral

Let $X$ be a topological space with measurable open sets, and let measures $\mu_n$ on $X$ satisfy
the [large deviation principle](../large-deviation-principle/satisfies-ldp.md) with a rate
function $I$, not necessarily good. Let $F : X \to \mathbb{R}$ be continuous with $|F| \le C$, let
$K \subseteq X$ be closed and $u \in \mathbb{R}$ with $F(x) - I(x) \le u$ for every $x \in K$.
Then for every $t > u$, for all sufficiently large $n$,
$\int_K e^{nF} \, d\mu_n \le e^{nt}$. The proof is the finite-partition argument applied to the
closed sets $K \cap F^{-1}[a_j, a_{j+1}]$.
