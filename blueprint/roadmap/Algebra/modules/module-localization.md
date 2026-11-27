# Localization of a module at a multiplicatively closed subset

Let $R$ be a commutative semiring, for instance a commutative ring with identity, let $S \subseteq R$ be a multiplicatively closed subset, so that $1 \in S$ and $st \in S$ whenever $s, t \in S$, and let $M$ be an $R$-module.

On $M \times S$ declare $(m, s) \sim (m', s')$ when there is some $t \in S$ with $ts'm = tsm'$. This is an equivalence relation. The *localization* $S^{-1}M$ is the set of equivalence classes, and the class of $(m, s)$ is written $m/s$. When $R$ is a ring and $M$ is an abelian group, the condition reads $t(s'm - sm') = 0$.

The operations are given by the formulas

$$\frac{m}{s} + \frac{m'}{s'} = \frac{s'm + sm'}{ss'}, \qquad \frac{r}{u}\cdot\frac{m}{s} = \frac{rm}{us} \quad (r \in R,\ u \in S).$$

These operations are well defined and make $S^{-1}M$ a module over the localized semiring $S^{-1}R$, which is the case $M = R$; when $R$ is a ring, $S^{-1}R$ is a ring. When $P$ is a prime ideal of $R$ and $S = R \setminus P$, one writes $M_P$ for $S^{-1}M$.

## Sources

- David Eisenbud, Commutative Algebra with a View Toward Algebraic Geometry, Graduate Texts in Mathematics 150, Springer-Verlag, 1995.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the relation on pairs: `LocalizedModule.r`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Module/LocalizedModule/Basic.lean#L53-L56.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the localization as the set of classes of pairs: `LocalizedModule`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Module/LocalizedModule/Basic.lean#L85-L89.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the action of the localized semiring, $(r/u)\cdot(m/s) = rm/(us)$: `LocalizedModule.mk_smul_mk`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Module/LocalizedModule/Basic.lean#L309-L311.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the commutative semiring structure on the localization of a commutative semiring: `CommSemiring R[S⁻¹]`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/RingTheory/OreLocalization/Ring.lean#L219-L225.
