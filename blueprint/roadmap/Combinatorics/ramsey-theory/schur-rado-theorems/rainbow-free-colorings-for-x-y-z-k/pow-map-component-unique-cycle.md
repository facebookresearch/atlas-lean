# Each component of the power digraph has exactly one cycle

Let $p$ be a prime and $k$ a
natural number, and let $G^k_p$ be the digraph on $\mathbb{Z}/p\mathbb{Z}$ with edges
$a \to a^k$, so that $m$ steps lead from $a$ to $a^{k^m}$. Call $a$ a cycle vertex if
$a^{k^r} = a$ for some $r > 0$, and say that $a$ and $b$ lie in the same component if
$a^{k^m} = b^{k^n}$ for some $m, n \ge 0$. Then every $a$ has a cycle vertex $a^{k^m}$ among its
iterates, and if two cycle vertices $a$ and $b$ lie in the same component, then $b = a^{k^m}$
for some $m \ge 0$. Thus every component of $G^k_p$ contains exactly one cycle.

## Sources

- Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 12.
