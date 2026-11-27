# The generic rank of the f4 matrix is the common independent-set number

Let $E$ be a finite edge set and fix the topology and admixture proportions, hence the
[contrast columns](contrast-matrix.md) $u_e\in\mathbb R^n$ and $v_e\in\mathbb R^r$.
Assume the [drift-model factorization](f4-matrix-eq-contrast-mul-diagonal-mul-t.md)

$$F(\ell)=U\operatorname{diag}(\ell)V^{\mathsf T}=\sum_{e\in E}\ell_e u_e v_e^{\mathsf T},$$

and let the lengths vary as independent coordinates in a nonempty open set
$\Omega\subseteq(0,\infty)^E$. Define $c$ as the largest $|S|$ for which both indexed
families $(u_e)_{e\in S}$ and $(v_e)_{e\in S}$ are linearly independent. These are families
indexed by edges, not sets obtained by collapsing equal columns. Then
$\operatorname{rank}F(\ell)\le c$ for every $\ell\in\Omega$, and there is a nonzero real
polynomial $p$ in the edge-length variables such that

$$p(\ell)\ne0\quad\Longrightarrow\quad\operatorname{rank}F(\ell)=c.$$

Consequently equality holds on a relatively open dense subset of $\Omega$ whose complement
has Lebesgue measure zero. If $c=0$, then $F$ is identically zero and one can take $p=1$;
this includes an empty edge set or a zero row or column dimension.

## Depends on

- [Drift-model factorization of the f4 matrix through weight contrasts](f4-matrix-eq-contrast-mul-diagonal-mul-t.md)
- [Lineage-weight contrasts against a reference population](contrast-matrix.md)

## Proof depends on

- [Matroid intersection for abstract rank functions](../../../Combinatorics/matroid-theory/matroid-intersection-theorem/exists-common-indep-of-cut-le.md), for the rank-partition characterization below, not for the Cauchy–Binet argument.

## Expansion

Fix orders on the finite index sets. For row sets $P,Q$ of size $k$, Cauchy–Binet gives

$$\det F(\ell)[P,Q]=\sum_{\substack{S\subseteq E\\|S|=k}}\det U[P,S]\,\det V[Q,S]\prod_{e\in S}\ell_e.$$

Distinct edge subsets give distinct squarefree monomials. For fixed $P,Q$, this polynomial
is nonzero exactly when one coefficient $\det U[P,S]\det V[Q,S]$ is nonzero. Some pair
$P,Q$ has such a coefficient exactly when there is a common independent indexed family of
size $k$: full column rank of $U[:,S]$ and $V[:,S]$ supplies their respective nonzero minors.
Thus every minor of size greater than $c$ vanishes, giving the rank bound (with the usual
matrix-dimension bound when there are no such minors). If $c>0$, choose a nonzero $c$-minor
as $p$. Its zero set contains every rank-drop point; it need not equal the rank-drop locus.

A nonzero real polynomial has a zero set of measure zero. One proves this by induction on
the number of variables: outside the null set where a selected nonzero coefficient
polynomial vanishes, each one-variable fiber has finitely many roots. Fubini on bounded
boxes, followed by a countable union, gives the null-set conclusion. The zero set is closed
by continuity and has empty interior, since a nonempty open box has positive measure.
Restricting to the open set $\Omega$ proves the stated genericity. The zero-variable case
is a nonzero constant; the empty determinant and empty monomial are both $1$.

For the associated linear matroids, put
$r_U(A)=\dim\operatorname{span}\{u_e:e\in A\}$ and similarly for $r_V$. Then

$$c=\min_{A\subseteq E}\bigl(r_U(A)+r_V(E\setminus A)\bigr).$$

For any common independent $I$, split it into $I\cap A$ and $I\setminus A$ to obtain
$|I|\le r_U(A)+r_V(E\setminus A)$. Conversely, the two linear rank functions obey the
cardinality bound, monotonicity and submodularity. Apply the linked matroid-intersection
theorem with $k$ equal to the minimum to obtain a common independent set of size at least
$k$. This is a rank-partition formula, not an identification with a graph or trek separator
in an admixture graph; no such graph-cut interpretation is established here.

The exact algebraic examples distinguish generic rank from rank at every positive point:

- For $U=(1\;1)$ and $V=(1\;-1)$, $c=1$ and $F(\ell)=(\ell_1-\ell_2)$. Its rank is zero
  exactly when $\ell_1=\ell_2$, and one otherwise.
- For $U=V=I_2$, $c=2$ and $F(\ell)=\operatorname{diag}(\ell_1,\ell_2)$ has rank two for
  every positive length pair.

In the first example, the constrained family $\ell=(t,t)$ with $t>0$ has rank zero
throughout. It is not open in the two-dimensional length space. The generic conclusion
therefore does not transfer automatically to coupled Wright–Fisher-derived lengths or
other lower-dimensional parameter families; a separate argument must show that a witness
minor remains nonzero after restriction. The examples concern the matrix factorization
and do not assert that arbitrary contrast matrices or free lengths are realized by every
population-genetic model.

The factorization is an explicit application hypothesis. Soraggi–Wiuf's general stochastic
admixture-graph formula also includes covariance terms between undirected root edges;
those terms cannot silently be replaced by a free diagonal length matrix. A general bridge
from that framework to this drift model is not asserted by this result.

## Related topics

- [The f4 matrix rank is at most the number of edges seen by both sides](rank-f4-matrix-le-support.md)

## Sources

- S. Sullivant, K. Talaska and J. Draisma, "Trek separation for Gaussian graphical models",
  Annals of Statistics 38 (2010), 1665–1685, <https://doi.org/10.1214/09-AOS760>,
  Lemma 3.2 and its proof (the distinct diagonal-monomial argument),
  <https://arxiv.org/abs/0812.1938>. Theorem 2.8 concerns Gaussian graphical models;
  the fixed-contrast matrix statement above is the elementary algebraic consequence proved here,
  not an invocation of its trek-separation conclusion.
- S. Soraggi and C. Wiuf, "General theory for stochastic admixture graphs and F-statistics",
  Theoretical Population Biology 125 (2019), 56–66, <https://doi.org/10.1016/j.tpb.2018.12.002>;
  preprint <https://arxiv.org/abs/1807.07593>, Definition 5, Lemma 1 and equation (9),
  for the stochastic-graph framework and its F-statistic decomposition, not the generic-rank theorem.
