# Lie Markov models with purine/pyrimidine symmetry

**Symmetry group.** The permutations of $\{A,G,C,T\}$ that preserve the grouping $AG\mid CT$ form the group

$$\mathcal G=\{e,(AG),(CT),(AG)(CT),(AC)(GT),(AT)(CG),(ACGT),(ATGC)\},$$

isomorphic to the dihedral group of order $8$ (the wreath product of $\mathfrak S_2$ with itself). A [Lie Markov model](stochastic-cone-of-a-lie-markov-model.md) has $\mathcal G$ symmetry if it has a basis permuted by conjugation with every $K_\sigma$, $\sigma\in\mathcal G$ (Definition 3.1); such a model also has the symmetry of every subgroup, and every [$\mathfrak S_4$-symmetric model](lie-markov-models-with-full-nucleotide-symmetry.md) qualifies.

**Theorem 4.1.** As a $\mathcal G$-module, the $4$-state general rate-matrix model decomposes into irreducibles as

$$\mathfrak L_{GM}\cong 2\,\mathrm{id}\oplus\mathrm{sgn}\oplus\zeta_1\oplus 2\,\zeta_2\oplus 3\,\xi,$$

with $12=2+1+1+2+6$, where $\mathrm{id},\mathrm{sgn},\zeta_1,\zeta_2$ are one-dimensional and $\xi$ is the two-dimensional irreducible representation.

**Theorem 5.1 (dimension one).** The two trivial summands are spanned by commuting rate matrices $B_1^{\mathrm{id}}$ (transitions $A\leftrightarrow G$, $C\leftrightarrow T$) and $B_2^{\mathrm{id}}$ (all transversions). There is a continuum of one-dimensional $\mathcal G$-symmetric Lie Markov models $\langle aB_1^{\mathrm{id}}+bB_2^{\mathrm{id}}\rangle$ with $a,b\ge 0$, i.e. Jukes–Cantor-like models with a fixed transition/transversion ratio.

**Classification (Section 5).** For each admissible decomposition in each dimension $d\le 12$, all complex Lie subalgebras of $\mathfrak L_{GM}$ with that decomposition and a stochastic basis are listed, each named $d.r$ by its dimension $d$ and the number $r\ge d$ of rays of its stochastic cone. The hierarchy contains the Kimura 3ST model (3.3a), the Felsenstein 81 model (4.4a), new three- and four-parameter transition/transversion models (3.3b, 3.3c, 4.4b), an HKY-like five-parameter model (5.6b), and model 6.6, which becomes the strand-symmetric model after relabelling by $(GT)$. Because the classification works for any pairing, the same hierarchy describes models preserving $AC\mid GT$ or complementation $AT\mid GC$.

## Expansion

Branching the $\mathfrak S_4$ decomposition $\{4\}\oplus2\{31\}\oplus\{2^2\}\oplus\{21^2\}$ down to $\mathcal G$ by the character tables gives Theorem 4.1. A $\mathcal G$-symmetric model is a sum of permutation modules $\langle\mathcal G/H\rangle$ for subgroups $H$, so its possible decompositions are finite in number; for each, the Lie subalgebras are found by direct computation of brackets among the symmetry-adapted basis vectors. A model containing a rate matrix with all off-diagonal entries positive, such as $aB_1^{\mathrm{id}}+bB_2^{\mathrm{id}}$ with $a,b>0$, automatically has a stochastic basis, since adding a large multiple of it to any basis makes every element non-negative. Rays of the stochastic cones come in $\mathcal G$-orbits of size $1$, $2$, $4$ or $8$ and preserve the totals of transition and transversion rates.

## Depends on

- [Stochastic cone of a Lie Markov model](stochastic-cone-of-a-lie-markov-model.md)
- [Lie Markov models with full nucleotide symmetry](lie-markov-models-with-full-nucleotide-symmetry.md)

## Sources

- Jesús Fernández-Sánchez, Jeremy G. Sumner, Peter D. Jarvis and Michael D. Woodhams, "Lie Markov models with purine/pyrimidine symmetry", arXiv:1206.1401 (2012), Introduction (definition of the purine/pyrimidine group and the table of selected models), Section 3 (Definition 3.1), Section 4 (Theorem 4.1), Section 5 (Theorem 5.1 and the model list), <https://doi.org/10.48550/arXiv.1206.1401>. Published version: Journal of Mathematical Biology 70(4) (2015), 855–891, <https://doi.org/10.1007/s00285-014-0773-z>; locators above refer to the arXiv version.
