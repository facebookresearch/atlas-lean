# Semialgebraic description of the two-state general Markov model on the 3-leaf tree

**Model.** Let $T$ be the tree with leaves $1,2,3$ joined to a central root $r$. The $k$-state general Markov model GM($k$) assigns a root distribution $\boldsymbol\pi = (\pi_1,\dots,\pi_k)$ and $k\times k$ Markov matrices $M_1, M_2, M_3$ on the three edges (nonnegative entries, rows summing to $1$). The joint distribution of the leaf states is the $k\times k\times k$ tensor

$$ P(i,j,\ell) = \sum_{m=1}^k \pi_m\, M_1(m,i)\, M_2(m,j)\, M_3(m,\ell), \qquad \text{i.e. } P = \mathrm{Diag}(\boldsymbol\pi)\cdot(M_1,M_2,M_3). $$

Parameters are *nonsingular* if every node marginal has no zero entry and every $M_e$ is invertible. For a tensor $P$ write $P_{\cdot\cdot+}$, $P_{\cdot+\cdot}$, $P_{+\cdot\cdot}$ for the $k\times k$ matrices obtained by summing over the third, second, first index, $P_{i\cdot\cdot}$, $P_{\cdot i\cdot}$, $P_{\cdot\cdot i}$ for the slices with that index fixed to $i$, $\mathrm{adj}$ for the classical adjoint, and $\mathrm{Flat}_{1|23}(P)$ (and similarly) for the $k\times k^2$ flattening. For $k=2$ let $\Delta(P)$ be Cayley's hyperdeterminant of the $2\times2\times2$ tensor $P = (a_{ijk})$:

$$ \Delta = \big(a_{111}^2a_{222}^2 + a_{112}^2a_{221}^2 + a_{121}^2a_{212}^2 + a_{122}^2a_{211}^2\big) - 2\big(a_{111}a_{112}a_{221}a_{222} + a_{111}a_{121}a_{212}a_{222} + a_{111}a_{122}a_{211}a_{222} + a_{112}a_{121}a_{212}a_{221} + a_{112}a_{122}a_{221}a_{211} + a_{121}a_{122}a_{212}a_{211}\big) + 4\big(a_{111}a_{122}a_{212}a_{221} + a_{112}a_{121}a_{211}a_{222}\big), $$

which satisfies $\Delta(P\cdot(g_1,g_2,g_3)) = \det(g_1)^2\det(g_2)^2\det(g_3)^2\,\Delta(P)$.

**Theorem.** A $2\times2\times2$ tensor $P$ is the leaf distribution of GM(2) on $T$ for some stochastic parameters if and only if its entries are nonnegative, sum to $1$, and one of the following holds.

1. *(Nonsingular case.)* $\Delta(P) > 0$; $\det(P*_i\mathbf 1) \neq 0$ for each index $i = 1,2,3$ (each two-leaf marginal matrix is invertible); all leading principal minors of

$$ \det(P_{\cdot\cdot+})\, P_{+\cdot\cdot}^T\, \mathrm{adj}(P_{\cdot\cdot+})\, P_{\cdot+\cdot} $$

   are positive; and all principal minors of the six matrices $\det(P_{\cdot\cdot+})P_{i\cdot\cdot}^T\mathrm{adj}(P_{\cdot\cdot+})P_{\cdot+\cdot}$, $\det(P_{\cdot\cdot+})P_{+\cdot\cdot}^T\mathrm{adj}(P_{\cdot\cdot+})P_{\cdot i\cdot}$ and $\det(P_{+\cdot\cdot})P_{\cdot+\cdot}\,\mathrm{adj}(P_{+\cdot\cdot})P_{\cdot\cdot i}^T$ ($i=1,2$) are nonnegative. Then $P$ arises from nonsingular parameters, unique up to swapping the two states at the root.
2. *(Singular case.)* $\Delta(P) = 0$ and all $2\times2$ minors of at least one of $\mathrm{Flat}_{1|23}(P)$, $\mathrm{Flat}_{2|13}(P)$, $\mathrm{Flat}_{3|12}(P)$ vanish. Then $P$ arises only from singular parameters, and from infinitely many of them if all entries of $P$ are positive.

For strictly positive parameters the same statement holds with positive entries of $P$ and with "nonnegative principal minors" in case 1 replaced by "positive leading principal minors". For general $k$, nonsingular stochastic leaf distributions are characterized by the analogous quadratic-form conditions together with the equalities and non-vanishing conditions that identify the $GL(k,\mathbb C)^3$-orbit of $\mathrm{Diag}(\mathbf 1)$.

## Depends on

- [Edge flattenings have rank at most the number of states](../../../not-yet-classified/general-markov-flattening/rank-flatten-leaf-dist-le.md)

## Expansion

A complex $2\times2\times2$ tensor lies in the $GL(2,\mathbb C)^3$-orbit of $D=\mathrm{Diag}(1,1)$ iff $\Delta \neq 0$, and a real one lies in the $GL(2,\mathbb R)^3$-orbit iff $\Delta > 0$; nonsingular parameters give $P = D\cdot(\mathrm{diag}(\boldsymbol\pi)M_1, M_2, M_3)$, so $\Delta(P) > 0$. The orbit condition only produces complex or real nonsingular parameters; recovering them explicitly, the products $P_{+\cdot\cdot}^T\mathrm{adj}(P_{\cdot\cdot+})P_{\cdot+\cdot}$ and their slice versions are congruent to diagonal matrices whose entries are the root weights and the Markov matrix entries, so by Sylvester's law of inertia positive definiteness (positive leading principal minors) is equivalent to positivity of the root distribution and positive semidefiniteness (nonnegative principal minors) to nonnegativity of the Markov entries. In the singular case the orbit classification of $2\times2\times2$ real tensors leaves only the orbit of $\mathrm{Diag}(1,0)$ (tensor rank $1$) and the orbits of tensors with one zero slice (multilinear rank $(2,2,1)$), each of which is realized by explicit families of singular stochastic parameters. The 3-leaf descriptions are the building blocks for the $n$-leaf case, glued through flattening rank conditions on edges.

## Sources

- Elizabeth S. Allman, John A. Rhodes, Amelia Taylor, "A semialgebraic description of the general Markov model on phylogenetic trees", arXiv:1212.1200 (2012), Section 2.1 (model), Section 2.3 (nonsingular parameters), Section 3 (hyperdeterminant orbit theorem, the $k$-state quadratic-form theorem, and the GM(2) theorems for nonnegative and positive parameters). <https://doi.org/10.48550/arXiv.1212.1200>. Published version: SIAM Journal on Discrete Mathematics 28(2) (2014), 736–755, <https://doi.org/10.1137/120901568>; locators above refer to the arXiv version.
