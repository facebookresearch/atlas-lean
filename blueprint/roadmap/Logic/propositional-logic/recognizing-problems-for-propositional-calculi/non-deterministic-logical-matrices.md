# Non-deterministic logical matrices and their decision problems

A non-deterministic matrix interprets each connective as a multi-function on truth values; the logic it defines makes $A$ follow from $\Gamma$ when every valuation designating $\Gamma$ designates $A$, and two Nmatrices are equivalent when they define the same logic.

**Nmatrices.** A *non-deterministic matrix* (Nmatrix) over a propositional signature $\Sigma$ is a triple $\mathbb{M} = \langle V, D, \cdot_{\mathbb{M}}\rangle$ with a non-empty set $V$ of truth values, a set $D \subseteq V$ of designated values, and for every $k$-ary connective $\circledcirc \in \Sigma$ an interpretation $\circledcirc_{\mathbb{M}}\colon V^k \to 2^V \setminus \{\varnothing\}$. It is *finite* when $V$ and $\Sigma$ are finite, and it is a (deterministic) matrix when every $\circledcirc_{\mathbb{M}}(x_1, \dots, x_k)$ is a singleton. A *valuation* is a map $v$ from formulas to $V$ with $v(\circledcirc(A_1, \dots, A_k)) \in \circledcirc_{\mathbb{M}}(v(A_1), \dots, v(A_k))$.

**The logic of an Nmatrix.** $\Gamma \vdash_{\mathbb{M}} A$ if every valuation $v$ with $v(\Gamma) \subseteq D$ has $v(A) \in D$. A *theorem* is a formula $A$ with $\varnothing \vdash_{\mathbb{M}} A$. Two $\Sigma$-Nmatrices are *equivalent* if $\vdash_{\mathbb{M}_1} = \vdash_{\mathbb{M}_2}$.

**Decision problems.** For the class $\mathsf{NMatr}$ of finite Nmatrices:

- $\exists\mathsf{Thm}(\mathsf{NMatr})$: given a finite signature $\Sigma$ and a finite $\Sigma$-Nmatrix $\mathbb{M}$, decide whether $\vdash_{\mathbb{M}}$ has a theorem;
- $\mathsf{Eqv}(\mathsf{NMatr})$: given a finite signature $\Sigma$ and finite $\Sigma$-Nmatrices $\mathbb{M}_1$, $\mathbb{M}_2$, decide whether they are equivalent.

The consequence problem, deciding $\Gamma \vdash_{\mathbb{M}} A$ for finite $\Gamma$, is decidable (in coNP) for finite Nmatrices, and equivalence of finite deterministic matrices is decidable.

## Depends on

None.

## Proof depends on

None.

## Sources

- Carlos Caleiro, Pedro Filipe and Sérgio Marcelino, "Equivalence of finite non-deterministic logical matrices is undecidable", *Studia Logica*, 2025, doi:[10.1007/s11225-025-10212-x](https://doi.org/10.1007/s11225-025-10212-x). Numbering of the version read, arXiv:2412.14057v1: Section 2.2 (matrices and Nmatrices) and Section 2.3 (computational problems).
