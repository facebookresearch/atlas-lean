# Cusp forms on Γ₁(N) with integral q-expansions form a lattice

Let $k \ge 1$ and $N \ge 1$, let $S$ be the space of cusp forms of weight $k$ on $\Gamma_1(N)$, with $q$-expansions
$f = \sum_{n \ge 1} a_n q^n$, and for a subfield $K$ of $\mathbb{C}$ let $S(K)$ be the $K$-vector space of the $f \in S$ with all
$a_n \in K$. For $d \in (\mathbb{Z}/N\mathbb{Z})^*$ let $R_d$ be the operator $f \mapsto f|_k \gamma$ on $S$, for any
$\gamma \in \Gamma_0(N)$ whose lower right entry is congruent to $d$ modulo $N$, with
$(f|_k\gamma)(z) = (cz + d')^{-k} f\bigl(\frac{az + b}{cz + d'}\bigr)$ for
$\gamma = \left(\begin{smallmatrix} a & b \\ c & d' \end{smallmatrix}\right)$. Let $L$ be the set of $f \in S$ such that, for every
$d \in (\mathbb{Z}/N\mathbb{Z})^*$, all the $q$-expansion coefficients of $f|R_d$ lie in $\mathbb{Z}$. Then $L$ is a free
$\mathbb{Z}$-module of finite rank, and for every subfield $K$ of $\mathbb{C}$ the map $K \otimes_{\mathbb{Z}} L \to S$,
$c \otimes f \mapsto c f$, is injective with image $S(K)$. In particular $S = \mathbb{C} \otimes_{\mathbb{Z}} L$, and $L$ spans
$S(\mathbb{Q})$ over $\mathbb{Q}$.

The proof is that of (2.7.1)–(2.7.2) in Deligne–Serre. As $R_1$ is the identity, $L \subset S(\mathbb{Q})$. For
$f \in S(\mathbb{Q})$, [bounded denominators](bounded-denominators-of-rational-cusp-forms.md) give an integer $m \ge 1$ with
$(mf)|R_d = m (f|R_d)$ integral for every $d$, that is $mf \in L$; so $\mathbb{Q} \otimes_{\mathbb{Z}} L \to S(\mathbb{Q})$ is onto, and
it is injective since $L$ is a subgroup of the $\mathbb{Q}$-vector space $S(\mathbb{Q})$. By the
[rational structure](rational-structure-on-cusp-forms.md) on $S$, $S(\mathbb{Q})$ has finite dimension $r = \dim_{\mathbb{C}} S$. A
form is determined by its $q$-expansion, so the coefficient maps $f \mapsto a_n$ separate the points of $S(\mathbb{Q})$, and
$r$ of them, $a_{n_1}, \dots, a_{n_r}$, form a basis of its dual; then $f \mapsto (a_{n_1}, \dots, a_{n_r})$ embeds $L$ into
$\mathbb{Z}^r$, so $L$ is free of rank at most $r$, and of rank $r$ since it spans $S(\mathbb{Q})$. Finally
$K \otimes_{\mathbb{Z}} L = K \otimes_{\mathbb{Q}} (\mathbb{Q} \otimes_{\mathbb{Z}} L) = K \otimes_{\mathbb{Q}} S(\mathbb{Q})$, which maps
isomorphically onto $S(K)$ by item 2 of the rational structure. (Deligne and Serre separate the points of $S(\mathbb{Q})$ by
the $n$-th coefficients of all the expansions $(f|R_d)_\infty$.)

## Depends on

- [Cusp form](../../../../../modular-forms-q-series/modular-forms/cusp-form.md), for the space $S$
- [Congruence subgroup $\Gamma_1(N)$](../../../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma1.md)
- [Congruence subgroup $\Gamma_0(N)$](../../../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma0.md), for the operators $R_d$
- [Free module](../../../../../../LinearAlgebra/bases-and-dimension/free-module.md), for the free $\mathbb{Z}$-module $L$

## Proof depends on

- [Cusp forms on Γ₁(N) with rational q-expansions span all cusp forms](rational-structure-on-cusp-forms.md), for $\dim_{\mathbb{Q}} S(\mathbb{Q}) = \dim_{\mathbb{C}} S$ and $S(K) = K \otimes_{\mathbb{Q}} S(\mathbb{Q})$
- [Bounded denominators of cusp forms on Γ₁(N) with rational q-expansions](bounded-denominators-of-rational-cusp-forms.md), for a multiple of each form of $S(\mathbb{Q})$ lying in $L$

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): Proposition 2.7, (2.7.1)–(2.7.2), and its proof, p. 512.
