# Tijdeman's theorem on runs of vanishing power sums

This settles [Erdős Problem 974 on runs of vanishing power sums](vanishing-power-sum-runs-configuration.md) in the affirmative: its statement holds.

Tijdeman's published theorem treats distinct $z_1, \dots, z_N$ with $z_1 = 1$: if the power sums
$s_k = \sum_i z_i^k$ have runs of $N - 1$ consecutive zeros (two runs already suffice), then for odd $N$ the
$z_i$ are the $N$-th roots of unity, and for even $N$ they are the vertices of two regular $(N/2)$-gons with
the same circumscribed circle centred at the origin. The linked statement does not assume distinctness, but
its hypothesis of infinitely many runs forces it, so it follows from the distinct case.

Let $N \ge 1$, $z_1 = 1$, and suppose infinitely many $k \ge 0$ start a run
$s_k = \dots = s_{k+N-2} = 0$. For $N = 1$ the conclusion is immediate. Let $N \ge 2$, let $W$ be the set of
distinct nonzero values among the $z_i$, write $\mu(w) \ge 1$ for the multiplicity of $w \in W$, and let
$d = |W|$; then $1 \in W$, so $d \ge 1$. Suppose the $z_i$ are not distinct and nonzero, so that
$d \le N - 1$. Choose a start $k \ge 1$. For $0 \le j \le d - 1$ the index $k + j$ lies in the run and is
positive, so zero entries contribute nothing and
$0 = s_{k+j} = \sum_{w \in W} \mu(w) w^k \cdot w^j$. This is a square Vandermonde system in the distinct
values $w \in W$, so every weight $\mu(w) w^k$ vanishes, which is impossible for the entry $w = 1$. Hence
the $z_i$ are distinct and nonzero.

For $N = 2$ the conclusion is then direct: $1 + z_2^k = 0$ for some $k$ gives $|z_2| = 1$ and $z_2 \ne 1$,
and $\{1, z_2\}$ is the required configuration with $c = z_2$. For $N \ge 3$, Tijdeman's theorem applies,
since infinitely many runs supply the runs it needs. For odd $N$ its conclusion is the required
configuration. For even $N$, the common circle passes through $z_1 = 1$, so it is the unit circle; the
regular $(N/2)$-gon containing $1$ is the set of $(N/2)$-th roots of unity; the other is the set of
$(N/2)$-th roots of $c = w^{N/2}$ for any of its vertices $w$, with $|c| = 1$; and $c \ne 1$ because the
two polygons share no vertex, the $z_i$ being distinct.

The distinctness step uses one run with a positive start; the rest is the published distinct case. For
$N \ge 2$ every run starts at a positive index, since $s_0 = N \ne 0$, so the same reduction already works
with only two runs: either run gives distinctness and nonvanishing, and the two runs then satisfy the
hypothesis of the published distinct-input theorem. The problem page separately credits a proof of the
two-run statement without distinctness to Hu, Tang and Zhang, in its discussion.

## Sources

- T. F. Bloom, Erdős Problems, Problem \#974, https://www.erdosproblems.com/974 (status PROVED (LEAN)); resolution: R. Tijdeman, On a conjecture of Turán and Erdős, Indag. Math. (1966), 374-383, for distinct $z_i$, erdosproblems.com/974: true even with two such runs; for odd $n$ the $z_i$ are the $n$-th roots of unity, for even $n$ the vertices of two regular $(n/2)$-gons with the same circumscribed circle centred at the origin; first proved by Tijdeman, with an independent proof by Hu, Tang and Zhang in the comments (whose Proposition 1 removes Tijdeman's assumption that the $z_i$ are distinct), https://www.erdosproblems.com/974.
