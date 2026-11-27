# Monadicity of finite non-deterministic logical matrices is undecidable

For finite logical matrices it is decidable whether any two truth values can be separated by a formula in one variable, but once connectives may be interpreted as multi-functions no algorithm decides this property; as a consequence the multi-functions expressible in a finite non-deterministic matrix are not computable.

**Non-deterministic matrices.** Let $\Sigma$ be a propositional signature. A *$\Sigma$-Nmatrix* $\mathbb M=\langle A,\cdot_{\mathbb M},D\rangle$ has a set $A$ of truth values, a set $D\subseteq A$ of designated values, and for each $k$-ary connective $\circledcirc$ a multi-function $\circledcirc_{\mathbb M}:A^k\to\wp(A)\setminus\{\emptyset\}$; it is *finite* if $A$ and $\Sigma$ are finite, and it is a logical matrix when all values $\circledcirc_{\mathbb M}(a_1,\dots,a_k)$ are singletons. A *valuation* $v$ maps formulas to $A$ with $v(\circledcirc(\varphi_1,\dots,\varphi_k))\in\circledcirc_{\mathbb M}(v(\varphi_1),\dots,v(\varphi_k))$. The induced logic is $\Gamma\vdash_{\mathbb M}\varphi$ if every valuation designating all of $\Gamma$ designates $\varphi$; $\varphi$ is a *theorem* if $\emptyset\vdash_{\mathbb M}\varphi$. A formula $\varphi$ in one variable $p$ defines the multi-function $\varphi_{\mathbb M}(a)=\{v(\varphi):v(p)=a\}$, and it *separates* $a$ and $b$ if one of $\varphi_{\mathbb M}(a)$, $\varphi_{\mathbb M}(b)$ is contained in $D$ and the other in $A\setminus D$. $\mathbb M$ is *monadic* if every pair of distinct truth values is separated by some formula in one variable.

**Theorem (Filipe, Caleiro and Marcelino).**

1. The problem of determining whether a given finite $\Sigma$-Nmatrix is monadic is undecidable (Theorem 4.8).
2. For each deterministic counter machine $\mathcal C$ there is an effectively constructed finite Nmatrix $\mathbb M_{\mathcal C}$ whose theorems are exactly the closed formulas encoding finite computations of $\mathcal C$ (Theorem 4.6).

Consequently, there is no algorithm computing the set of unary multi-functions expressible in a given finite Nmatrix (Corollary 4.9). For a finite (deterministic) matrix, monadicity is decidable by generating all expressible unary functions. Monadicity matters because for a finite monadic Nmatrix an analytic axiomatization of the induced logic can be produced automatically.

## Depends on

None.

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

From a deterministic counter machine $\mathcal C$ one builds a finite Nmatrix $\mathbb M_{\mathcal C}$ whose closed formulas can encode sequences of configurations; non-determinism lets every valuation refute a formula unless it encodes the actual computation of $\mathcal C$ from the initial configuration, and an infectious non-designated error value propagates mistakes. Thus $\vdash_{\mathbb M_{\mathcal C}}$ has a theorem exactly when $\mathcal C$ halts. A second construction transforms any finite Nmatrix $\mathbb M$ with at least two truth values and an infectious non-designated value into an Nmatrix $\mathbb M_{\mathsf m}$ that is monadic if and only if $\vdash_{\mathbb M}$ has theorems. Composing the two reduces the halting problem for counter machines to monadicity.

## Sources

- P. Filipe, C. Caleiro and S. Marcelino, "Monadicity of non-deterministic logical matrices is undecidable", in *Proceedings of the 10th International Conference on Non-Classical Logics: Theory and Applications (NCL 2022)*, Electronic Proceedings in Theoretical Computer Science 358, pp. 55–67, 2022, doi:[10.4204/EPTCS.358.5](https://doi.org/10.4204/EPTCS.358.5); read in arXiv:2204.06725v1 ([arXiv](https://arxiv.org/abs/2204.06725v1)), whose numbering is used: the definitions of Nmatrices, valuations and monadicity in the preliminaries, Theorem 4.6, the construction of $\mathbb M_{\mathsf m}$ in the subsection "From theoremhood to monadicity", Theorem 4.8, Corollary 4.9, and the introduction for the deterministic case.
