# The word problem of a finitely presented amenable group is unsolvable on every exponentially generic set

If $G$ is a finitely presented amenable group with unsolvable word problem, then for every finite generating set no algorithm solves the word problem on an exponentially generic set of words.

Let $W$ be the set of words over a finite generating set of $G$ and $W_n$ the words of length at most $n$. A set $X \subseteq W$ is exponentially generic if $|X \cap W_n| / |W_n|$ tends to $1$ exponentially fast. If $G$ is a finitely presented amenable group with unsolvable word problem, then for any choice of finite generating set the word problem of $G$ is not solvable on any exponentially generic subset of $W$ (Theorem 2.3 of the source).

The source poses as an open problem the construction of a finitely presented group whose word problem is undecidable on every generic set of inputs.

## Depends on

- [Solvable word problem](word-problem-solvable.md)
- [Group](../../group-basics/group.md)
- [Amenable group (Følner condition)](../../geometric-group-theory/amenable-groups/is-amenable.md)

## Proof depends on

None.

## Expansion

Suppose a correct partial algorithm $\mathcal{A}$ halts on an exponentially generic set $D$. Run $\mathcal{A}$ on all products $w v$ with $v$ enumerated among the words trivial in $G$ (possible since $G$ is finitely presented); if this halts for every $w$, the word problem is solvable. Otherwise some $w$ has $w v \notin D$ for every trivial $v$, so $W_n \setminus D$ contains $w V_{n - |w|}$, where $V_k$ is the set of trivial words of length $k$. Amenability gives $(|V_k| / |W_k|)^{1/k} \to 1$ along even $k$ (Kesten, Grigorchuk), which contradicts the exponential decay of $|W_n \setminus D| / |W_n|$. The Kesten–Grigorchuk cogrowth criterion for amenability has no page here. Finitely presented amenable groups with unsolvable word problem exist (Kharlampovich's solvable groups).

## Sources

- R. Gilman, A. Miasnikov and D. Osin, "Exponentially generic subsets of groups", Illinois Journal of Mathematics 54 (2010), no. 1, 371–388, https://doi.org/10.1215/ijm/1299679753; read in arXiv:1007.0552v1, whose numbering is used here (Theorem 2.3 and the closing problem of arXiv:1007.0552v1).
