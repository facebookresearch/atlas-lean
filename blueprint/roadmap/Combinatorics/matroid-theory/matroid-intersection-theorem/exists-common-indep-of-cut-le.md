# Matroid intersection for abstract rank functions

Let $E$ be a finite subset of a type
$\alpha$, let $k$ be a natural number, and let $r_1, r_2$ be functions from the finite subsets of
$\alpha$ to $\mathbb{N}$ such that, for $i = 1, 2$ and all finite $X, Y \subseteq \alpha$, we have
$r_i(X) \le |X|$, $r_i(X) \le r_i(Y)$ whenever $X \subseteq Y$, and
$r_i(X \cap Y) + r_i(X \cup Y) \le r_i(X) + r_i(Y)$. If every $X \subseteq E$ satisfies
$k \le r_1(X) + r_2(E \setminus X)$, then there is a set $I \subseteq E$ with
$r_1(I) = r_2(I) = |I|$ and $|I| \ge k$.

Proved by induction on $E$, via deletion and contraction.
