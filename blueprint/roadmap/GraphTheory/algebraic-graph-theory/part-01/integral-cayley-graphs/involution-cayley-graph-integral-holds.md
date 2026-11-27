# Cayley graphs on normal sets of involutions are integral

Let $G$ be a finite group and let
$R \subseteq G$ be a set of involutions ($r^2 = 1$ and $r \ne 1$ for every $r \in R$) that is
closed under conjugation ($g r g^{-1} \in R$ for all $r \in R$ and $g \in G$) and generates $G$.
Then the Cayley graph $\mathrm{Cay}(G, R)$, whose vertices are the elements of $G$ with distinct
$x$ and $y$ adjacent when $x^{-1} y \in R$ or $y^{-1} x \in R$, is integral: every eigenvalue of
its integer adjacency matrix (every complex root of the characteristic polynomial of that matrix)
is an integer.

The Kourovka Archive proof: every eigenvalue of $\mathrm{Cay}(G, R)$ has the form
$\frac{1}{\chi(1)} \sum_{r \in R} \chi(r)$ for an irreducible character $\chi$ of $G$; this number
is rational because characters take integer values on involutions, and it is an algebraic integer.

## Sources

- E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.50 (D. V. Lytkina); resolution: (a) D. O. Revin, letter of 21 April 2018; A. Abdollahi, letter of 3 May 2018; (b) W. Guo, D. V. Lytkina, V. D. Mazurov and D. O. Revin, Integral Cayley graphs, Algebra Logic 58 (2019), no. 4, 297-305, doi:10.1007/s10469-019-09550-2, Kourovka Archive, Problem 19.50: (a) Yes, with a character-theoretic proof in the Archive (each eigenvalue is (1/χ(1)) ∑_{r ∈ R} χ(r), rational since characters take integer values on involutions); (b) Yes, https://arxiv.org/abs/1401.0300v49.
