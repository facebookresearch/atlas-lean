# Zenkov's rank bound fails (Kourovka 21.150)

Call a subgroup elementary abelian if it is
abelian and there is a prime $p$ with $x^p = 1$ for all its elements $x$. There are a finite group
$G$, elementary abelian subgroups $A$ and $B$ of $G$ with $A$ normal, $A \cap B = 1$ and
$\langle A, B \rangle = G$, and an element $a \in A$ whose centralizer $C_B(a)$ in $B$ is trivial,
such that, for $H = \langle a, B \rangle$, with centre $Z(H)$ and derived subgroup $H' = [H, H]$,
some finite generating set of $B$ has fewer elements than every finite generating set of
$Z(H) \cap H'$ (here $Z(H)$ is viewed as a subgroup of $G$).

Counterexample (Monticone; van Doorn, Judin, Monticone and Morrison, Theorem 9.1):
$A = \mathbb{F}_3[x, y]/(x, y)^3$, $B = \langle 1 + x, 1 + y \rangle$ acting by multiplication,
$G = A \rtimes B$ and $a = 1$; then $C_B(a) = 1$, while
$Z(H) \cap H' = \langle x^2, xy, y^2 \rangle$ has rank $3 > 2 = \operatorname{rank} B$. The 21st
issue of the Kourovka Notebook marks 21.150 solved ("No, not always").

## Sources

- E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 21.150 (V. I. Zenkov); resolution: P. Monticone, letter of 21 March 2026 and solution note, Kourovka Notebook site; W. van Doorn, E. Judin, P. Monticone and D. Morrison, On some problems from the Kourovka Notebook, preprint, arXiv:2607.17477 (2026), Kourovka Notebook (21st issue), Problem 21.150: No, not always: A = F₃[x, y]/I³ (I = (x, y)), B = ⟨1 + x, 1 + y⟩ acting by multiplication, G = A ⋊ B, a = 1; then C_B(a) = 1 and Z(H) ∩ H' = ⟨x², xy, y²⟩ has rank 3 while B has rank 2; van Doorn-Judin-Monticone-Morrison, Theorem 9.1, https://arxiv.org/abs/2607.17477.
