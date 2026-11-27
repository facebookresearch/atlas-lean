# Iterative median-sign recovery of differential components

Take expected relative abundances $Q_{k,i}$, $k=1,2$, $i\in[d]$, with $Q_{1,i}+Q_{2,i}>0$, and let $I_0$ be the largest reference set ($Q_{1,i}=bQ_{2,i}$ on $I_0$), assumed to satisfy $|I_0|>d/2$; let $I_1=[d]\setminus I_0$. (Any two reference sets with more than $d/2$ elements share the factor $b$, so their union is again one and the largest is unique. The theorem fails for a reference set that is not the largest: for $d=3$ and $Q_1=Q_2$ uniform, $\{1,2\}$ is a reference set, but the procedure returns $\hat I_1=\emptyset\neq\{3\}$.) For $I\subseteq[d]$ define the renormalized differences and their median

$$
R_i(I)=\frac{Q_{1,i}}{\sum_{j\in I}Q_{1,j}}-\frac{Q_{2,i}}{\sum_{j\in I}Q_{2,j}}\quad(i\in I),\qquad M(I)=\operatorname{Median}\{R_i(I):i\in I\}.
$$

Start from $U_{(0)}=\emptyset$, $V_{(0)}=[d]$ and repeat. Let $W_{(t)}$ be the components of $V_{(t)}$ whose $R_i(V_{(t)})$ has a sign different from $M(V_{(t)})$: all nonzero ones if $M=0$, the negative and zero ones if $M>0$, the positive and zero ones if $M<0$. Set $U_{(t+1)}=U_{(t)}\cup W_{(t)}$ and $V_{(t+1)}=V_{(t)}\setminus W_{(t)}$, and stop when $W_{(t)}=\emptyset$, at $t=T$.

**Theorem (noiseless recovery).** With $\hat I_0=V_{(T)}$ and $\hat I_1=U_{(T)}$,

$$
T\le|I_1|+1,\qquad \hat I_0=I_0,\qquad \hat I_1=I_1.
$$

With data, the median and signs come from Welch two-sample $t$ statistics on renormalized empirical proportions. The resulting robust differential abundance (RDB) test controls the family-wise error asymptotically, $\mathbb P(\hat I_1\cap I_0\neq\emptyset)\le\alpha+o(1)$, under the paper's dependence and signal assumptions.

## Depends on

- [Identifiability of the reference-based differential abundance hypothesis](identifiability-of-the-reference-based-differential-abundance-hypothesis.md)

## Proof sketch

Whenever $I_0\subseteq V$, all reference components share the ratio $b(V)$ between their renormalized proportions, so they have one common sign of $R_i(V)$. Because they are a strict majority of $V$, the median carries that sign. Every removed component therefore has the wrong sign and is truly differential, and $I_0$ is never touched. Renormalizing on the smaller set moves $b(V)$ toward the differential components still left, so each round removes at least one of them until none remain.

## Sources

- Shulei Wang, "Robust differential abundance test in compositional data", *Biometrika* 110 (2023), 169–185, <https://doi.org/10.1093/biomet/asac029>. Preprint version: arXiv:2101.08765 (2021), Section 3 (iterative procedure, Theorem 1 noiseless recovery, Theorem 2 FWER control), <https://doi.org/10.48550/arXiv.2101.08765>.
