# The Hecke operators on cusp forms on Γ₁(N) commute and preserve the integral lattice

Let $k \ge 1$ and $N \ge 1$, let $S$ be the space of cusp forms of weight $k$ on $\Gamma_1(N)$, with $q$-expansions
$f = \sum_{n \ge 1} a_n q^n$, and for $d \in (\mathbb{Z}/N\mathbb{Z})^*$ let $R_d$ be the operator $f \mapsto f|_k \gamma$ on $S$, for
any $\gamma \in \Gamma_0(N)$ whose lower right entry is congruent to $d$ modulo $N$, with
$(f|_k\gamma)(z) = (cz + d')^{-k} f\bigl(\frac{az + b}{cz + d'}\bigr)$ for
$\gamma = \left(\begin{smallmatrix} a & b \\ c & d' \end{smallmatrix}\right)$. For a prime $p \nmid N$ let $T_p$ be the Hecke
operator, given on $q$-expansions by

$$f|T_p = \sum_{n \ge 1} a_{pn} q^n + p^{k-1} \sum_{n \ge 1} a_n(p)\, q^{pn}, \qquad f|R_p = \sum_{n \ge 1} a_n(p)\, q^n.$$

Let $L$ be the set of $f \in S$ such that, for every $d \in (\mathbb{Z}/N\mathbb{Z})^*$, all the $q$-expansion coefficients of
$f|R_d$ lie in $\mathbb{Z}$. Then the operators $T_p$, $p \nmid N$, and $R_d$, $d \in (\mathbb{Z}/N\mathbb{Z})^*$, map $S$ into itself
and commute with one another, $R_d R_{d'} = R_{dd'}$, and they map $L$ into $L$.

Given the first two assertions, the last is the computation of Deligne–Serre. Let $f \in L$ and write
$f|R_d = \sum_n a_n(d) q^n$, with all $a_n(d) \in \mathbb{Z}$. Then $(f|R_{d'})|R_d = f|R_{dd'}$ has integral coefficients for
every $d$, so $f|R_{d'} \in L$. And $(f|T_p)|R_d = (f|R_d)|T_p$, where $f|R_d$ has the coefficients $a_n(d)$ and
$(f|R_d)|R_p = f|R_{pd}$ has the coefficients $a_n(pd)$, so that by the formula above

$$(f|T_p)|R_d = \sum_{n \ge 1} a_{pn}(d)\, q^n + p^{k-1} \sum_{n \ge 1} a_n(pd)\, q^{pn},$$

which has integral coefficients; so $f|T_p \in L$.

## Depends on

- [Cusp form](../../../../../modular-forms-q-series/modular-forms/cusp-form.md), for the space $S$
- [Congruence subgroup $\Gamma_1(N)$](../../../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma1.md)
- [Congruence subgroup $\Gamma_0(N)$](../../../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma0.md), for the operators $R_d$

## Proof depends on

Its proof uses the inputs listed under Expansion.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the Hecke operator $T_p$ on the cusp forms of weight $k$ on $\Gamma_1(N)$, which Deligne–Serre define by the isogenies of
  degree $p$ (§2.3) and identify with the classical operator (§2.4), and its effect (2.5.1) on $q$-expansions, the
  formula above ([7], VII, §4, as cited in §2.5);
- the relations $T_p T_{p'} = T_{p'} T_p$ and $T_p R_d = R_d T_p$ (§2.3);
- the relation $R_d R_{d'} = R_{dd'}$, from the isomorphism $\Gamma_0(N)/\Gamma_1(N) \to (\mathbb{Z}/N\mathbb{Z})^*$ given by the
  lower right entry modulo $N$ (§1.5), or from $(f|R_d)(E, \alpha) = f(E, d\alpha)$ (formula (2.2.1)).

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): §1.4, p. 508, for the operators $R_d$; §1.5, p. 509, for
  $\Gamma_0(N)/\Gamma_1(N) \cong (\mathbb{Z}/N\mathbb{Z})^*$; formula (2.2.1), p. 510; §2.3, p. 511 ("Les $\mathrm{T}_p$ commutent
  entre eux, et commutent aux $\mathrm{R}_d$"); §2.4 and formula (2.5.1), p. 511; Proposition 2.7, (2.7.1), and its
  proof, p. 512.
- P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*, in *Modular functions of one variable
  II*, Lecture Notes in Math. 349, Springer (1973), 143–316: VII, §4, as cited in Deligne–Serre (1974), p. 512; not
  read.
