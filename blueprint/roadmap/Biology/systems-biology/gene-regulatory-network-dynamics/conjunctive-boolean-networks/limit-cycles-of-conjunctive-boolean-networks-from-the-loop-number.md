# Limit cycles of conjunctive Boolean networks from the loop number

**Setting.** A *conjunctive Boolean network* on $n$ nodes is a map $f = (f_1, \dots, f_n) \colon \mathbb{F}_2^n \to \mathbb{F}_2^n$ with each $f_i$ a conjunction $x_{i_1} \wedge \dots \wedge x_{i_{j_i}}$ of variables; *disjunctive* networks use $\vee$ instead. Its *dependency graph* has an arc $j \to i$ when $x_j$ occurs in $f_i$, with Boolean adjacency matrix $A$. The *loop number* of a nontrivial strongly connected graph is the gcd of the lengths of its directed cycles; for a general graph it is the lcm of the loop numbers of its nontrivial strongly connected components. The *height* $h(f)$ is the least $s$ with $f^s(u)$ periodic for all $u$, and the *period* $p(f)$ is the lcm of the lengths of all limit cycles. Let $A(m)$ be the set of states of exact period $m$.

**Theorem.**

1. *(Duality.)* The phase spaces of a disjunctive network $f$ and the conjunctive network $g$ with the same variable sets ($\vee$ replaced by $\wedge$) are isomorphic directed graphs.
2. *(Matrix powers.)* $A^s$ is the adjacency matrix of the dependency graph of $f^s$. If the loop number of $A$ is $c$ and its exponent is $k$ (the least $k$ with $A^{k+c} = A^k$), then $h(f) = k$ and $p(f)$ divides $c$.
3. *(Strongly connected case.)* Suppose the dependency graph is strongly connected with loop number $c$. If $c = 1$, the only limit cycles are the two fixed points $(0, \dots, 0)$ and $(1, \dots, 1)$. If $c > 1$ and $m \mid c$ with $m = \prod_{i=1}^r p_i^{k_i}$ (distinct primes, $k_i \ge 1$), then

    $$|A(m)| = \sum_{i_1 = 0}^{1} \cdots \sum_{i_r = 0}^{1} (-1)^{i_1 + \dots + i_r}\, 2^{p_1^{k_1 - i_1} \cdots p_r^{k_r - i_r}},$$

    and the number of limit cycles of length $m$ is $|A(m)|/m$.

4. *(Height bounds.)* In the strongly connected case, $h(f) \le (n-1)^2 + 1$ if $c = 1$ and $h(f) \le \max\{n - 1,\ \frac{n^2-1}{2} + \frac{n^2}{c} - 3n + 2c\}$ if $c > 1$; for any conjunctive network on $n$ nodes, $h(f) \le 2n^2 - 3n + 2$.
5. *(Typical behavior.)* The fraction of the $2^{n^2}$ conjunctive networks on $n$ nodes whose dependency graph is strongly connected with loop number $1$ tends to $1$, so almost all conjunctive networks have only the two fixed points as limit cycles.

## Expansion

For a conjunctive network, state $u$ evolves by Boolean matrix multiplication: $f(u)_i = 1$ iff all in-neighbors of $i$ are $1$, so iterating $f$ is taking Boolean powers of $A$. Powers of an irreducible Boolean matrix become periodic with period equal to the loop number after the exponent, which gives the height and period. With loop number $c$ the strongly connected graph splits into $c$ cyclically permuted classes on which the dynamics is a rotation of a binary word of length $c$; counting words of exact rotational period $m$ by inclusion–exclusion over the prime divisors of $m$ gives the formula. Such networks model gene regulation where a gene is on only if all its activators are on.

## Sources

- Abdul Salam Jarrah, Reinhard Laubenbacher and Alan Veliz-Cuba, "The Dynamics of Conjunctive and Disjunctive Boolean Network Models", Bulletin of Mathematical Biology 72 (2010), 1425–1447, <https://doi.org/10.1007/s11538-010-9501-z>; numbering as in arXiv:0805.0275: Theorem 1.3, Corollary 2.3, Lemma 2.7, Theorems 2.10–2.12, Theorem 3.8 and Corollary 3.9.
