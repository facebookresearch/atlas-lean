# Finiteness and cohomological dimension of Galois groups with restricted ramification

Let $F$ be a number field, $S \supseteq S_\infty$ a set of places of $F$ and $G_S$ the Galois group of the
maximal extension of $F$ unramified outside $S$.

1. **Cohomological dimension.** If $p$ is a prime with $S_p \subseteq S$, and $F$ is totally imaginary
   when $p = 2$, then $\operatorname{cd}_p(G_S) \le 2$.
2. **Finiteness.** Let $A$ be a $G_S$-module that is finitely generated as an abelian group, with torsion
   of order in $\mathbb{N}(S)$. If $S$ and $A$ are finite, then $H^n(G_S, A)$ is finite for every $n \ge 0$.
   If $S$ is finite or $A$ is torsion-free, then $H^1(G_S, A)$ is finite.
3. **High degrees.** If $A$ is finite of order in $\mathbb{N}(S)$, then for every $i \ge 3$ restriction is an
   isomorphism $H^i(G_S, A) \to \bigoplus_{v \text{ real}} H^i(F_v, A)$. In particular $H^i(G_S, A) = 0$ for
   $i \ge 3$ if $F$ is totally imaginary, or if the order of $A$ is odd.

## Depends on

- [Galois groups with restricted ramification and their modules](galois-groups-with-restricted-ramification.md)
- [Cohomological dimension of a profinite group](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/cohomological-dimension.md), for cohomological $p$-dimension

## Proof depends on

- [Global duality for Galois groups with restricted ramification](global-duality-for-galois-groups-with-restricted-ramification.md), for the cohomology of the $S$-units and the $p$-divisibility of $\mathcal{O}_S^\times$ (items 1 and 2), and for the global duality theorem and the exact sequence $0 \to A' \to I_S(A) \to C_S(A) \to 0$ of level-compact modules (item 3)
- [The Hochschild–Serre spectral sequence](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/discrete-coefficients/hochschild-serre-spectral-sequence.md), for the Hochschild–Serre spectral sequence, used in item 3
- [Properties of cohomological dimension](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/properties-of-cohomological-dimension.md), for the passage from $p$-Sylow subgroups, used in item 3
- [The long exact Tate cohomology sequence of level-compact modules](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/discrete-coefficients/long-exact-tate-cohomology-sequence-of-level-compact-modules.md) and [Tate cohomology of finite modules over groups of order divisible by ℓ^∞](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/discrete-coefficients/tate-cohomology-of-finite-modules.md), for the Tate cohomology of profinite groups of order divisible by $\ell^\infty$ (NSW (1.9.13), (1.9.15)), used in item 3

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition,
  version 2.3 (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: (8.3.18) Proposition
  ($\operatorname{cd}_p G_S \le 2$), (8.3.20) Theorem (finiteness), pp. 463–465; (8.6.10) (ii) (restriction to the
  real places is an isomorphism in degrees $\ge 3$) and its proof, pp. 489–491.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, Theorem 4.10 (c) and Corollary 4.15.
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses the finiteness and the vanishing for $\ell \ne 2$ in degrees $\ge 3$ as
  `ReciprocityTheory.Gal.GlobalFiniteness`, and the vanishing for totally imaginary fields as
  `GlobalTheory.Published.CohDimTwoGlobal`.
