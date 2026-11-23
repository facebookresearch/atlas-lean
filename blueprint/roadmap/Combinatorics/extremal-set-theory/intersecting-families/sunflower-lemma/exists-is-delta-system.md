# Erdős–Rado sunflower lemma

Let $F$ be a finite family of finite sets, each with exactly $w$ elements. If

$$|F| > w!\,(p-1)^w,$$

then $F$ contains a [Δ-system](is-delta-system.md) with $p$ petals: a subfamily $S \subseteq F$ with $|S| = p$ whose pairwise intersections are all equal.

The proof is by induction on $w$. Take a pairwise disjoint subfamily of maximal size. If it has $p$ members, they form a sunflower with empty kernel. Otherwise its union $U$ has at most $(p-1)w$ points and meets every member of $F$, so some point $x \in U$ lies in more than $(w-1)!\,(p-1)^{w-1}$ members; removing $x$ from them and applying the induction hypothesis gives a sunflower, to whose kernel $x$ is added back.

The bound is sharp up to the factor $w!$: the $(p-1)^w$ sets that contain exactly one element of each of $w$ disjoint blocks of size $p - 1$ contain no sunflower with $p$ petals. The [Alweiss–Lovett–Wu–Zhang bound](theorem-1-4.md) replaces $w!\,(p-1)^w$ by $(C p^3 \log w \log\log w)^w$, and the [Erdős–Szemerédi problem](conjecture.md) asks for bounds $c^n$ with $c < 2$ for families of arbitrary subsets of an $n$-set.

The lemma is the combinatorial step of Razborov's approximation method: it shows that a family of small cliques can be "plucked" to a bounded size with few errors.

## Related topics

- [Monotone circuit lower bound for clique](../../../../TheoryOfComputation/circuit-complexity/monotone-circuit-lower-bound-for-clique/README.md): Razborov's approximation method, where the lemma bounds the error of each approximation step.

## Sources

- P. Erdős and R. Rado, Intersection theorems for systems of sets, J. London Math. Soc. 35 (1960), 85-90.
- R. Alweiss, S. Lovett, K. Wu and J. Zhang, Improved bounds for the sunflower lemma, Ann. of Math. 194 (2021), arXiv:1908.08483v3, introduction.
