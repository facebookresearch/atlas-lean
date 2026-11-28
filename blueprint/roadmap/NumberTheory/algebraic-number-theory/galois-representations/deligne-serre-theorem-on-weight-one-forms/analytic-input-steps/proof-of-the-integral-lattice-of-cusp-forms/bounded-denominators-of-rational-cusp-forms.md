# Bounded denominators of cusp forms on Γ₁(N) with rational q-expansions

Let $k \ge 1$ and $N \ge 1$, let $S$ be the space of cusp forms of weight $k$ on $\Gamma_1(N)$, and for
$d \in (\mathbb{Z}/N\mathbb{Z})^*$ let $R_d$ be the operator $f \mapsto f|_k \gamma$ on $S$, for any $\gamma \in \Gamma_0(N)$ whose
lower right entry is congruent to $d$ modulo $N$, with $(f|_k\gamma)(z) = (cz + d')^{-k} f\bigl(\frac{az + b}{cz + d'}\bigr)$
for $\gamma = \left(\begin{smallmatrix} a & b \\ c & d' \end{smallmatrix}\right)$. Let $f \in S$ have all its $q$-expansion
coefficients in $\mathbb{Q}$. Then there is an integer $m \ge 1$ such that, for every $d \in (\mathbb{Z}/N\mathbb{Z})^*$, all the
$q$-expansion coefficients of $m \cdot (f|R_d)$ lie in $\mathbb{Z}$.

Deligne and Serre deduce this from the Tate curve being defined over $\mathbb{Z}((q)) \otimes \mathbb{Q}$ (Remarque 2.8): for a
form $f$ defined over a ring $R$ they set $f_\infty(q) = f(\mathbf{G}_m/q^{\mathbb{Z}}, \mathrm{Id})/(dt/t)^{\otimes k}$, an element of
$\mathbb{Z}((q)) \otimes R$ (§2.5), so that for $R = \mathbb{Q}$ its coefficients have a common denominator. Each $f|R_d$ again
has rational coefficients ([rational structure](rational-structure-on-cusp-forms.md), item 3), and a common multiple of
the denominators of the finitely many $f|R_d$ is an $m$ as above. They note that for $k \ge 2$ one may instead use
théorème 3.5.2 of Shimura's book, and bring weight $1$ to weight $13$ by multiplying by $\Delta$ (Remarque 2.8).

## Depends on

- [Cusp form](../../../../../modular-forms-q-series/modular-forms/cusp-form.md), for the space $S$
- [Congruence subgroup $\Gamma_1(N)$](../../../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma1.md)
- [Congruence subgroup $\Gamma_0(N)$](../../../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma0.md), for the operators $R_d$

## Proof depends on

- [Cusp forms on Γ₁(N) with rational q-expansions span all cusp forms](rational-structure-on-cusp-forms.md), for the rationality of the coefficients of each $f|R_d$

## Expansion

This node is still to be broken down. A good expansion states and links:

- the Tate curve $\mathbf{G}_m/q^{\mathbb{Z}}$ over $\mathbb{Z}((q)) = \mathbb{Z}[[q]][q^{-1}]$, with its invariant differential $dt/t$
  and its embedding $\mathrm{Id}$ of $\mu_N$ ([7], VII, §1, as cited in §2.5);
- the membership $f_\infty(q) \in \mathbb{Z}((q)) \otimes R$ for a form defined over a ring $R$ (§2.5), and the agreement of
  $f_\infty$ with the analytic $q$-expansion ([7], VII, §4, as cited in §2.5);
- or, for $k \ge 2$, théorème 3.5.2 of Shimura [24] (as cited in Remarque 2.8), with the passage from weight $1$ to weight
  $13$ by multiplication by $\Delta$.

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): §2.5, pp. 511–512; the proof of Proposition 2.7 ("les séries
  $(f \mid \mathrm{R}_d)_\infty(q)$ appartiennent à $\mathbf{Z}[[q]] \otimes \mathbf{Q}$, donc ont des dénominateurs bornés") and
  Remarque 2.8, p. 512.
- P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*, in *Modular functions of one variable
  II*, Lecture Notes in Math. 349, Springer (1973), 143–316: VII, §1 and VII, §4, as cited in Deligne–Serre (1974),
  p. 511; not read.
- G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Publ. Math. Soc. Japan 11, Iwanami
  Shoten and Princeton University Press, 1971: théorème 3.5.2, as cited in Deligne–Serre (1974), Remarque 2.8, p. 512;
  not read.
