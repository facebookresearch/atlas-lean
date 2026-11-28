# Polynomial-time strong refutation of semirandom Boolean CSPs

For every Boolean predicate $P$ other than the constant $1$ with $i(P)\ge 1$, a polynomial-time algorithm certifies that a semirandom CSP($P$) instance with $n^{(i(P)+1)/2}\mathrm{poly}(\log n)$ constraints is not $(1-\delta)$-satisfiable, where $i(P)\le k$ is the largest $t$ for which satisfying assignments support a $t$-wise uniform distribution. This matches the best bounds known for fully random instances.

**Theorem (strong refutation of all semi-random Boolean CSPs).** Fix a predicate $P:\{0,1\}^k\to\{0,1\}$. Let $r(P)=\mathbb{E}_x[P(x)]$ for uniformly random $x\in\{0,1\}^k$, let $d(P)$ be the degree of $P$ as a multilinear polynomial, and let $i(P)$ be the largest integer $t\le k$ for which $P^{-1}(1)$ supports a $t$-wise uniform distribution (one whose joint marginal on every $t$ coordinates is uniform). There is a polynomial-time algorithm that, given an $n$-variable semi-random instance of CSP($P$) (arbitrary $k$-tuples of variables, independent uniformly random negation patterns) with $m$ constraints, with high probability certifies:

1. when $P$ is not the constant $1$, $i(P)\ge 1$, and $m\ge n^{(i(P)+1)/2}\,\mathrm{poly}(\log n)$, that the instance is not $(1-\delta)$-satisfiable for some $\delta=\Omega_k(1)$ (no assignment satisfies a $1-\delta$ fraction of the constraints);
2. when $P$ is not a literal predicate ($d(P)\ne 1$) and $m\ge n^{d(P)/2}\,\mathrm{poly}((\log n)/\epsilon)$, that the instance is not $(r(P)+\epsilon)$-satisfiable.

(Theorem 1.1 in the source states both claims for every $P$; the first fails for the constant predicate $P\equiv 1$, which every assignment satisfies, and for every satisfiable $P$ with $i(P)=0$, while the second fails for literal predicates with $d(P)=1$, because $m\le n/k$ constraints on pairwise disjoint scopes are always satisfiable whatever their negations.)

The core case is $k$-XOR for $k\ge 2$ (Theorem 4.2 in the source leaves $k\ge 2$ implicit; its odd-$k$ proof invokes Theorem 4.1 with $\ell=n$, which needs $m>\ell/\epsilon^2=n/\epsilon^2$). A $k$-XOR instance $\phi=(V,E,r)$ has a variable set $V$, a multiset $E$ of $k$-element subsets of $V$, and signs $r:E\to\{\pm1\}$; an assignment $x\in\{\pm1\}^V$ satisfies $e\in E$ when $r(e)\prod_{v\in e}x_v=1$, and the instance is semi-random when $E$ is arbitrary and $r$ is uniformly random. For $k\ge 2$ and $0<\epsilon<1/2$ there is an absolute constant $K$ such that if $|V|=n$ and

$$
|E|=m\ge\frac{K\,n^{k/2}(\log n)^3}{\epsilon^5},
$$

then with high probability one can efficiently certify $\mathrm{val}_\phi\le1/2+\epsilon$.

## Expansion

Feige's XOR principle reduces refuting CSP($P$) to refuting the $k'$-XOR instances given by the Fourier expansion of $P$: the terms with $k'\ge 2$ are handled by the $k$-XOR theorem above (the new content is odd $k'\ge 3$, as even $k'$ already followed from Feige's discrepancy method), while any degree-$1$ ($1$-XOR) term has value $\frac{1}{2}+\frac{1}{2m}\sum_i|S_i|$ (where $S_i$ is the sum of signs on $x_i$), which is bounded directly by $\frac{1}{2}+\sqrt{cn\log n/m}\le\frac{1}{2}+\epsilon$ with high probability once $m\ge cn\log n/\epsilon^2$ (ensured by both thresholds since $i(P)\ge 1$ and $d(P)\ge 2$ each force $m\ge n\,\mathrm{poly}(\log n)$). For odd $k$, each constraint $e$ is split into one vertex $i$ and two disjoint $(k-1)/2$-sets $e_1,e_2$, producing a semi-random partitioned 2-XOR instance on vertex set $\binom{V}{(k-1)/2}$ with $\ell=n$ parts, whose constraint $(i,(e_1,e_2))$ is $x_{e_1}x_{e_2}y_i=r(e)$. The main technical theorem certifies $\mathrm{val}\le1/2+\epsilon$ for semi-random partitioned 2-XOR with $m\ge\max\{Kn\sqrt{\ell}(\log n)^3/\epsilon^5,\ \ell/\epsilon^2\}$ constraints and $\ell=O(\mathrm{poly}(n))$ parts.

That proof identifies a pseudorandomness property, bounded **butterfly degree** of pairs of vertices, under which the relevant matrices are sums of independent random matrices whose spectral norms the rectangular matrix Bernstein inequality controls. An arbitrary instance is decomposed into pseudorandom pieces and structured pieces (high-degree vertices are forked off into an auxiliary 2-XOR instance), and the structured pieces are bounded through the $\infty\to1$ norm, which semidefinite programming approximates within the Grothendieck constant $K_G<1.8$. The resulting certificate is spectral plus semidefinite, so it is captured by low-degree sum-of-squares. The sub-exponential-time extension of this endpoint to smoothed instances is the [smoothed CSP refutation theorem](smoothed-csp-refutation.md).

## Depends on

- [Semirandom and smoothed CSP instances and strong refutation](semirandom-and-smoothed-csps.md)

## Proof depends on

None.

## Sources

- Jackson Abascal, Venkatesan Guruswami, Pravesh K. Kothari, "Strongly refuting all semi-random Boolean CSPs", *SODA 2021*, 2021, arXiv:2009.08032v1, https://arxiv.org/abs/2009.08032 (Theorem 1.1; Theorem 1.2 with its detailed version Theorem 4.2 and its proof; Theorem 4.1; Definition 2.2; Lemma 3.3; Section 3 for the $k$-XOR model).
