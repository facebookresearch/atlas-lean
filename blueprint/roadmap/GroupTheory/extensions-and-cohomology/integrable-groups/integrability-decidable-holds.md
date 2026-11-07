# Integrability of finite groups is decidable

Integrable group tables form a decidable set: some
computable function decides, for every finite list $t = (t_0, \dots, t_{n-1})$ of finite lists of
natural numbers, whether there is a group structure on $\{0, \dots, n-1\}$ in which, for all
$i, j < n$, the product of $i$ and $j$ is the entry of $t_i$ at index $j$, counting from $0$ (an
entry missing from a short row is read as $0$), and which is isomorphic to the derived subgroup of
some finite group. That is, the decidability part of Kourovka Problem 21.32 has a positive answer.

Kalithasan and Thomas bound the order of some integral of an integrable finite group $G$ (their
Theorem 3.3 and its Corollary), which makes the problem decidable; the 21st issue of the Kourovka
Notebook marks 21.32 solved ("Yes, it is decidable, in nondeterministic quasi-polynomial time").
The complexity bound is not formalized.

## Sources

- E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 21.32 (P. J. Cameron); resolution: S. Kalithasan and V. Z. Thomas, On the decidability of the integrability of finite groups, preprint, arXiv:2602.18829 (2026), Theorem 3.3 (an integrable finite group G has an integral, a group with derived subgroup ≅ G, of order bounded in terms of |Aut(G)|, |Z(G)|, μ(G) and d(Z(G))) and its Corollary: integrability of a finite group is decidable; Kourovka Notebook (21st issue), Problem 21.32: Yes, it is decidable, in nondeterministic quasi-polynomial time, https://arxiv.org/abs/2602.18829.
