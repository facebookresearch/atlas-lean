# Polynomial calculus resolution PCR$_{\mathbb F}$

Polynomial calculus resolution $\mathrm{PCR}_{\mathbb F}$ refutes a system of polynomial equations over a field $\mathbb F$ by deriving $1$ with linear combinations and multiplication by variables, after adding Boolean axioms and a twin variable $\bar x_i$ for $1-x_i$; its size is the total number of monomials in the refutation.

Fix a field $\mathbb F$ and polynomials $f_1,\dots,f_m\in\mathbb F[x_1,\dots,x_n]$, each $f_i$ standing for the equation $f_i=0$. A *polynomial calculus* ($\mathrm{PC}_{\mathbb F}$) refutation of $(f_1,\dots,f_m)$ is a sequence of polynomials ending in $1$, each an axiom $f_i$ or derived from earlier lines by the rules

$$
\frac{f\qquad g}{\alpha f+\beta g}\ \ (\alpha,\beta\in\mathbb F)\qquad\qquad \frac{f}{x\cdot f}\ \ (x\text{ a variable}).
$$

Its *degree* is the maximum degree of a line and its *size* is the total number of monomials appearing in it. A $\mathrm{PCR}_{\mathbb F}$ refutation of $(f_1,\dots,f_m)$ is a $\mathrm{PC}_{\mathbb F}$ refutation of the system obtained by adding, for every variable $x_i$, the Boolean axiom $x_i^2-x_i$, a new *twin variable* $\bar x_i$, and the axioms $1-x_i-\bar x_i$ and $\bar x_i^2-\bar x_i$. A CNF is refuted through its clauses, each translated into a polynomial that vanishes exactly at the $0/1$ points satisfying it (with $\bar x_i=1-x_i$): in $\mathrm{PCR}_{\mathbb F}$ the clause $\bigvee_{i\in P}x_i\vee\bigvee_{i\in N}\neg x_i$ becomes the single monomial $\prod_{i\in P}\bar x_i\prod_{i\in N}x_i$, while in $\mathrm{PC}_{\mathbb F}$, which has no twin variables, it becomes $\prod_{i\in P}(1-x_i)\prod_{i\in N}x_i$, with $2^{|P|}$ monomials when expanded.

## Expansion

$\mathrm{PC}_{\mathbb F}$ and $\mathrm{PCR}_{\mathbb F}$ have the same degree, but the twin variables let $\mathrm{PCR}_{\mathbb F}$ write a clause with many positive literals as a single monomial in the $\bar x_i$, so a system can have much smaller $\mathrm{PCR}_{\mathbb F}$ than $\mathrm{PC}_{\mathbb F}$ refutations. Working with multilinear lines, that is in $\mathbb F[\vec x]/(\vec x^{\,2}-\vec x)$, increases neither size nor degree. Lower bounds for it include those for the [weak rank principle](weak-rank-pcr-f2-lower-bounds.md) and its [perfect matching encoding](weak-rank-perfect-matching-lower-bounds.md).

## Depends on

None.

## Proof depends on

None.

## Sources

- Michal Garlík, Svyatoslav Gryaznov, Hanlin Ren and Iddo Tzameret, "The Weak Rank Principle: Lower Bounds and Applications", *58th Annual ACM Symposium on Theory of Computing (STOC 2026)*, 2026, https://doi.org/10.1145/3798129.3800735; numbering as in arXiv:2608.08760v1 (Section 4.2, Definition 4.3 (polynomial calculus) and Definition 4.5 (PCR) and the remark after it; Section 5.2, proof of Lemma 5.16, clauses as monomials in the twin variables; Section 5, opening, multilinear lines).
