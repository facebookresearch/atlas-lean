# Disjoint augmenting paths in a symmetric difference (Hopcroft–Karp, Theorem 1)

Let $M$ and $N$ be matchings of a simple graph $G$ on a finite vertex set. Then there are $|N| - |M|$ pairwise vertex-disjoint [$M$-augmenting walks](is-augmenting-walk.md) whose edges all lie in the symmetric difference $M \oplus N$. Hopcroft and Karp state it for $|N| > |M|$; for $|N| \le |M|$ the truncated difference is $0$ and the statement is empty.

Their proof: every vertex meets at most one edge of $M \setminus N$ and one of $N \setminus M$, so the components of $(V, M \oplus N)$ are isolated vertices, even cycles and alternating paths; each component has at most one more edge of $N$ than of $M$, with equality exactly for $M$-augmenting paths, and the excesses add up to $|N| - |M|$.

It contains [Berge's lemma](berge-iff-not-exists-is-augmenting-walk.md) (take $N$ maximum) and is the counting step behind the bound of Hopcroft and Karp on the number of phases.

## Sources

- J. E. Hopcroft and R. M. Karp, "An $n^{5/2}$ algorithm for maximum matchings in bipartite graphs", *SIAM Journal on Computing* 2(4) (1973), 225–231, §2. Theorem 1.
