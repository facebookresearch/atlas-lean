# Inertness is decidable in free groups of finite rank (Kourovka Problem 19.104)

For every
natural number $n$, let $F_n$ be the free group on generators $x_0, \dots, x_{n-1}$, and give a
finitely generated subgroup of $F_n$ by a finite list of generating words in the letters
$x_i^{\pm 1}$. Then there is an algorithm deciding, for such a list, whether the subgroup $H$ it
generates is inert, that is, whether $r(H \cap K) \le r(K)$ for every subgroup $K$ of $F_n$. Here
the rank $r(L)$ of a subgroup $L$ is the least size of a finite generating set of $L$, and
$r(L) = \infty$ when $L$ is not finitely generated; "an algorithm" means that the predicate on
lists of words is computable.

Jaikin-Zapirain proved that a finitely generated subgroup of a free group is inert if and only if
it is compressed, and compressedness is known to be decidable.

## Sources

- E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 19.104 (E. Ventura); resolution: A. Jaikin-Zapirain, Free groups are L^2-subgroup rigid, preprint, arXiv:2403.09515 (2024), Corollary 1.3(2) (citing Kourovka 19.104): it is algorithmically decidable, for a finitely generated subgroup of a free group, whether it is inert (compressedness is decidable and equivalent to inertness by Corollary 1.2); the Kourovka Notebook (21st issue) marks 19.104 solved, https://arxiv.org/abs/2403.09515.
