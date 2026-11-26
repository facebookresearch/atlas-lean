# Sharpness of k-SAT lifetime and clause-replacement estimates

Fix $k\ge3$. For a set $S$ of Boolean assignments on $u$ variables, let $B_s(S,g)$ be the probability that after $g$ independent proper $s$-clauses there is no assignment from $S$ surviving. Put $L_s(S)=\sum_{m\ge0}(1-B_s(S,m))$, the sum of survival probabilities from the initial set (including time zero). Then:

* For every $\gamma<k/(k-1)$ and $D,A>0$, and every natural $N$, there are $u\ge\max(N,k)$ and nonempty $S$ with $B_{k-1}(S,1)\ge A u^{-(k-1)}$ and $D B_{k-1}(S,1)^{-\gamma}< L_k(S)$.
* There are dimensions $u_g$ and sets $S_g$, nonempty with $u_g\ge k$ for $g\ge2$, such that $B_{k-1}(S_g,1)-B_k(S_g,g)$ is asymptotically equivalent to $2^{-k}g^{-(k-1)}$ as $g\to\infty$.
* There is no real sequence $e_g=o(g^{-(k-1)})$ for which $B_{k-1}(S,1)-e_g\le B_k(S,g)$ for all $u\ge k$, nonempty $S$, and integers $g\ge2$.

**Conventions.** Use the proper-clause law and the iterative survival operator $f(S)\mapsto\mathbb E_C f(\{a\in S:a\text{ satisfies }C\})$. The lifetime uses its iterates applied to the nonempty-set indicator.

## Depends on

- [Proper-clause streams, survival and first failure](proper-clause-stream-and-survival.md)

## Proof depends on

Extremal assignment sets with large persistence for $k$-clauses relative to the one-clause kill probability at length $k-1$, and explicit asymptotics for the distinct replacement obstruction.

## Expansion

Treat the lifetime and replacement constructions separately. Prove the exhibited asymptotic has positive leading constant $2^{-k}$ and use its sign and exponent to contradict any universal little-$o$ error. There is no conclusion about a matching variance asymptotic at $k=3$.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SATSharpness.lean#L58-L73)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/235.md)
- [Accompanying manuscript: Variance of the Random $k$-SAT Hitting Time](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Variance-of-the-Random-k-SAT-Hitting-Time-September-27-2026/article.pdf)
- [Background: Friedgut, *Sharp thresholds of graph properties, and the k-sat problem*, Journal of the American Mathematical Society 12 (1999), 1017–1054](https://doi.org/10.1090/S0894-0347-99-00305-7)
