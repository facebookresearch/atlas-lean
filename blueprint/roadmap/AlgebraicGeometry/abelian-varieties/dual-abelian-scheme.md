# Dual abelian scheme

This node is still to be broken down: the statement is precise, and the proof is outlined below; its
inputs remain to be separated.

Let $S$ be a scheme and $A \to S$ an [abelian scheme](abelian-scheme.md) with zero section $e$. Its
relative Picard functor $\mathcal{P}ic_{A/S}$ sends an $S$-scheme $T$ to the group of isomorphism
classes of line bundles on $A \times_S T$ rigidified along $e_T$, and $\mathcal{P}ic^0_{A/S}$ is its
subfunctor of classes whose restrictions to the geometric fibres of $A \times_S T \to T$ lie in
$\operatorname{Pic}^0$.

**Theorem** (Mumford). $\mathcal{P}ic^0_{A/S}$ is represented by an abelian scheme $\hat A$ over
$S$, the *dual abelian scheme*, of the same relative dimension as $A$, projective over $S$ if $A$
is, and whose fibre over every point $s$ is the [dual abelian variety](dual-abelian-variety.md) of
$A_s$. The *Poincaré bundle* $\mathcal{P}$ on $A \times_S \hat A$, the rigidified line bundle that
corresponds to the identity of $\hat A$, is universal: for every $S$-scheme $T$ and every class in
$\mathcal{P}ic^0_{A/S}(T)$ there is a unique morphism $\alpha \colon T \to \hat A$ over $S$ such
that the class is that of $(\mathrm{id} \times \alpha)^* \mathcal{P}$. Its pull-back to $\hat A
\times_S A$ by the switch is the Poincaré bundle of $\hat A$, so that the morphism $A \to \hat{\hat
A}$ it classifies is an isomorphism (biduality).

A homomorphism $f \colon A \to B$ of abelian schemes over $S$ has a dual $\hat f \colon \hat B \to
\hat A$, classifying $(f \times \mathrm{id})^* \mathcal{P}_B$; if $f$ is an isogeny, then so is
$\hat f$, and there is an exact sequence $0 \to \operatorname{Ker}(f)^D \to \hat B \to \hat A \to
0$, with $\operatorname{Ker}(f)^D$ the Cartier dual of the finite flat group scheme
$\operatorname{Ker}(f)$ (Chai–Oort, (1.10), citing Oort's *Commutative Group Schemes*, Theorem
19.1). For $f = n_A$ this identifies $\hat A[n]$ with the Cartier dual of $A[n]$.

Robert's proof: $A \to S$ is proper and smooth with geometrically connected fibres, hence
cohomologically flat in dimension zero, so $\mathcal{P}ic_{A/S}$ is a separated algebraic space
whose torsion component $\mathcal{P}ic^\tau_{A/S}$ is proper; Mumford proves that it is smooth, by
showing with the group law that the obstructions to lifting line bundles vanish. So it is an abelian
algebraic space, hence an abelian scheme by Raynaud's theorem; since $\operatorname{Pic}^\tau =
\operatorname{Pic}^0$ for an abelian variety, $\mathcal{P}ic^\tau_{A/S} = \mathcal{P}ic^0_{A/S}$;
the universal rigidified line bundle exists because $A$ has the section $e$; and biduality can be
checked on the fibres, where it is biduality of abelian varieties.

A good expansion has pages for the three inputs of this proof that the linked pages do not supply:
the smoothness of $\mathcal{P}ic^\tau_{A/S}$ for an abelian scheme (Mumford, *Geometric Invariant
Theory*, Proposition 6.7, as cited by Robert); the equality $\operatorname{Pic}^\tau =
\operatorname{Pic}^0$ for abelian varieties, that is, the torsion-freeness of their Néron–Severi
groups (a class $L$ with $L^n \in \operatorname{Pic}^0$ has $n \varphi_L = 0$, hence $\varphi_L =
0$, as $\operatorname{Hom}(A, A^\vee)$ has no torsion); and the duality theorem for isogeny kernels
over a general base (Oort, *Commutative Group Schemes*, Theorem 19.1, as cited by Chai–Oort, (1.10);
over a field, van der Geer–Moonen, Theorem (7.5)). The general Picard representability theorems are
linked below.

## Depends on

- [Abelian scheme](abelian-scheme.md)
- [Dual abelian variety](dual-abelian-variety.md), for $\operatorname{Pic}^0$ and the fibres of $\hat A$
- [Isogenies of abelian schemes](isogenies-of-abelian-schemes.md), for isogenies and the finite flat
  kernels whose Cartier duals appear
- [Finite locally free group schemes and Cartier duality](deformations-and-p-divisible-groups/finite-locally-free-group-schemes-and-cartier-duality.md),
  for the Cartier dual $\operatorname{Ker}(f)^D$ of a finite flat kernel

## Proof depends on

- [Representability of relative Picard functors](representability-of-picard-functors.md), for the
  theorems of Artin, Grothendieck and Raynaud used above
- [Dual abelian variety](dual-abelian-variety.md), for biduality on the fibres
- [Finite locally free group schemes and Cartier duality](deformations-and-p-divisible-groups/finite-locally-free-group-schemes-and-cartier-duality.md),
  for its item 3, the description by characters of the line bundles with trivial pull-back along a
  quotient by a finite locally free group scheme (van der Geer–Moonen, Proposition (7.4), which is
  stated over a base), the core of the identification $\operatorname{Ker}(\hat f) \cong
  \operatorname{Ker}(f)^D$

## Sources

- D. Robert, *Theory of abelian varieties and their moduli spaces*, draft book (version of 7 March
  2023), <https://www.math.u-bordeaux.fr/~damienrobert/pro/publications/books/avtheory.pdf>:
  Definition 2.3.1 and Theorem 2.3.2, pp. 12–13; §2.3.2 and Theorem 2.3.7 (Mumford) with its proof,
  pp. 13–15 (citing Mumford's *Geometric Invariant Theory*, Proposition 6.7, for smoothness).
- C.-L. Chai and F. Oort, "Moduli of abelian varieties and p-divisible groups: density of Hecke
  orbits, and a conjecture of Grothendieck", lecture notes, arXiv:math/0701479 (version 1): (1.10)
  (duality theorem for abelian schemes, citing F. Oort, *Commutative Group Schemes*, Lecture Notes
  in Mathematics 15, Springer, 1966, Theorem 19.1) and (10.12) (the dual abelian scheme $A^t$,
  Mumford's $\hat A$, after *Geometric Invariant Theory*, 6.8).
- D. Mumford, *Geometric Invariant Theory*, Ergebnisse der Mathematik 34, Springer, 1965: §6.1–6.3,
  Proposition 6.7, as cited above.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states the existence of a dual abelian scheme over every scheme, of the same relative dimension,
  with a line bundle that makes each of the two abelian schemes the dual of the other, as
  `GlobalTheory.Published.DualAbelianScheme`.
