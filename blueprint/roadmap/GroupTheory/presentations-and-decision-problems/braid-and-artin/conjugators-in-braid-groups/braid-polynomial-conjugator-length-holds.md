# Braid groups have polynomially short conjugators

For $n \in \mathbb{N}$, let $B_{n+1}$ be
the braid group on $n + 1$ strands, realized as the Artin group of the Coxeter matrix of type
$A_n$, with standard generators $\sigma_1, \dots, \sigma_n$. A braid word is an element of the
free group on $\sigma_1, \dots, \sigma_n$, and its length $|u|$ is the length of its freely reduced
form. For every $n$ there are natural numbers $C$ and $d$ such that for all braid words $u$ and $v$
whose braids are conjugate in $B_{n+1}$ there is a braid word $w$ with
$|w| \le C (\max(|u|, |v|) + 1)^d$ such that $w u w^{-1}$ and $v$ represent the same braid.

This answers the stronger question of Kourovka Problem 19.81 positively: the Kourovka Archive
answers "Yes, there is such a conjugator, even for any mapping class groups", citing Tao's
linearly bounded conjugator property for mapping class groups (Theorem B: a conjugator of length
at most $K(|f| + |g|)$).

## Sources

- E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.81 (V. Shpilrain); resolution: J. Tao, Linearly bounded conjugator property for mapping class groups, Geom. Funct. Anal. 23 (2013), no. 1, 415-466 (arXiv:1106.2341), Theorem B: for a finite generating set of the mapping class group of a surface of finite type there is K such that conjugate f, g have a conjugator ω with |ω| ≤ K(|f| + |g|); Kourovka Archive, Problem 19.81: Yes, there is such a conjugator, even for any mapping class groups, https://arxiv.org/abs/1106.2341.
