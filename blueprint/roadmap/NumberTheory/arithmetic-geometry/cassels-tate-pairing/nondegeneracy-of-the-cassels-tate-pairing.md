# Nondegeneracy of the Cassels–Tate pairing

This node is still to be broken down. It covers the theorem of Cassels and Tate that the kernels of the
[Cassels–Tate pairing](cassels-tate-pairing-of-an-abelian-variety.md) are the maximal divisible subgroups, following
the proof in Milne's *Arithmetic Duality Theorems*, Chapter I, §6.

Let $K$ be a number field, $A$ an [abelian variety](../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md)
over $K$ and $A^\vee$ its [dual abelian variety](../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md),
and let $\langle\,,\rangle \colon \text{Ш}(K, A) \times \text{Ш}(K, A^\vee) \to \mathbb{Q}/\mathbb{Z}$ be the Cassels–Tate
pairing. Then:

- an element $a \in \text{Ш}(K, A)$ satisfies $\langle a, a' \rangle = 0$ for all $a' \in \text{Ш}(K, A^\vee)$ if and only
  if $a$ lies in the maximal divisible subgroup $\text{Ш}(K, A)_{\mathrm{div}}$;
- an element $a' \in \text{Ш}(K, A^\vee)$ satisfies $\langle a, a' \rangle = 0$ for all $a \in \text{Ш}(K, A)$ if and
  only if $a'$ lies in $\text{Ш}(K, A^\vee)_{\mathrm{div}}$.

So the pairing induces a nondegenerate pairing
$\text{Ш}(K, A)/\text{Ш}(K, A)_{\mathrm{div}} \times \text{Ш}(K, A^\vee)/\text{Ш}(K, A^\vee)_{\mathrm{div}} \to \mathbb{Q}/\mathbb{Z}$.
Milne states it one set of primes at a time: for every integer $m \ge 1$, the left and right kernels of the pairing
between the $m$-primary components $\text{Ш}(K, A)(m)$ and $\text{Ш}(K, A^\vee)(m)$ are their divisible subgroups.
The two forms agree because the groups are torsion, a torsion group is the direct sum of its $\ell$-primary
components, the pairing vanishes between components for different primes, and the maximal divisible subgroup of a
torsion group is the sum of those of its primary components.

## Expansion

Fix $m$, and a finite set $S$ of places containing the archimedean places, the places of bad reduction and those
above the primes dividing $m$; write $A_m = A[m](K_S)$ and $A^\vee_m = A^\vee[m](K_S)$, which are dual finite
$G_S$-modules through the Weil pairing $e_m$. A good expansion has pages for the three lemmas of Milne's proof and
the final count:

1. (Milne, Lemma I.6.15.) An element $(a_v) \in \bigoplus_{v \in S} H^1(K_v, A_m)$ is orthogonal, under the sum of the
   local pairings $\mathrm{inv}_v(a_v \cup a'_v)$, to the image of the Selmer group
   $S^{(m)}_S(K, A^\vee) \subseteq H^1(G_S, A^\vee_m)$ if and only if it is the sum of an element of the image of
   $\prod_{v \in S} H^0(K_v, A)$ (Tate cohomology at the archimedean places) and an element of the image of $H^1(G_S, A_m)$; by duality from the Poitou–Tate sequence
   for $A_m$ and Tate local duality for $A$.
2. (Milne, Lemma I.6.16.) If $\text{Ш}_0(K, A)$ denotes the subgroup of elements of $\text{Ш}(K, A)$ that become divisible
   by $m$ in $H^1(G_S, A(K_S))$, there is an exact sequence
   $0 \to \text{Ш}_0(K, A) \to \text{Ш}(K, A) \to \text{Ш}^2_S(K, A_m)$.
3. (Milne, Lemma I.6.17, the key lemma.) An element $a \in \text{Ш}_0(K, A)$ lies in $m\,\text{Ш}(K, A)$ if and only if
   $\langle a, a' \rangle = 0$ for all $a' \in \text{Ш}(K, A^\vee)[m]$; the proof modifies a lift of $a$ by a global
   class found through item 1, the obstruction being exactly $\langle a, a' \rangle$ by the definition of the pairing.
4. The conclusion (Milne, end of the proof of Theorem I.6.13 (a)): items 2 and 3, the Poitou–Tate duality between
   $\text{Ш}^2_S(K, A_m)$ and $\text{Ш}^1_S(K, A^\vee_m)$ and a diagram chase give injections
   $\text{Ш}(K, A)/m^n\text{Ш}(K, A) \to (\text{Ш}(K, A^\vee)[m^n])^*$, hence in the limit the left kernel is the
   $m$-divisible part; the right kernel follows by comparing the finite orders
   $[\text{Ш}(K, A)(m) : \text{Ш}(K, A)(m)_{\mathrm{div}}]$ for $A$, $A^\vee$ and $A^{\vee\vee} \cong A$.

For elliptic curves and $m$ prime, $\text{Ш}^2_S(K, A_m) = 0$, so $\text{Ш}_0 = \text{Ш}$ and the argument is
shorter (Milne, Remark I.6.18).

Milne builds the pairing from the $e_m$-pairing of the Cartier duality of $A[m]$ and $A^\vee[m]$, while the
[construction page](cassels-tate-pairing-of-an-abelian-variety.md) uses the Weil pairing as Poonen and Stoll define it;
transferring the proof uses the comparison of the two, listed in the expansion of that page. Replacing $e_m$ by its
inverse changes the pairing by a sign, which does not change its kernels.

## Depends on

- [The Cassels–Tate pairing of an abelian variety](cassels-tate-pairing-of-an-abelian-variety.md)

## Proof depends on

- [The Cassels–Tate pairing of an abelian variety](cassels-tate-pairing-of-an-abelian-variety.md), whose definition gives the obstruction in item 3
- [Selmer groups and the torsion of the Shafarevich–Tate group of an abelian variety](selmer-groups-of-abelian-varieties.md), for the passage to $G_S$ (its item 4) and for the finiteness of $\text{Ш}(K, A)[m]$ and of $\text{Ш}(K, A)(m)$ modulo its divisible subgroup (its item 3), used in the final count
- [Poitou–Tate duality](../../algebraic-number-theory/galois-representations/galois-cohomology-of-number-fields/poitou-tate-duality.md), for the duality between $\text{Ш}^1_S(K, A^\vee_m)$ and $\text{Ш}^2_S(K, A_m)$
- [Poitou–Tate exact sequence](../../algebraic-number-theory/galois-representations/galois-cohomology-of-number-fields/poitou-tate-exact-sequence.md), for the exactness at $P^1(G_S, A_m)$ used in item 1
- [Tate local duality for abelian varieties](../../algebraic-number-theory/galois-representations/galois-cohomology-of-local-fields/tate-local-duality-for-abelian-varieties.md), for the dual of $\bigoplus_{v \in S} H^1(K_v, A^\vee)$ and its compatibility with the local dualities of $A_m$ (its items 2 to 4), in item 1
- [Local Tate duality](../../algebraic-number-theory/galois-representations/galois-cohomology-of-local-fields/local-tate-duality.md), for the local pairings of $A_m$ and $A^\vee_m$ in item 1
- [Dual abelian variety](../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md), for the Cartier duality of $A[m]$ and $A^\vee[m]$ (its item 3) and biduality (its item 4), used in item 4

## Sources

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, Theorem 6.13 (a) (p. 82: "The left and right kernels of the canonical pairing
  $\text{Ш}^1(K, A)(m) \times \text{Ш}^1(K, A^t)(m) \to \mathbb{Q}/\mathbb{Z}$ are the divisible subgroups"), its proof through
  Lemmas 6.15–6.17 (pp. 86–89), Remark 6.18 (p. 89), and the Notes (p. 93: proved by Cassels for elliptic curves and by
  Tate in general); Theorem 4.10 (p. 56) for the Poitou–Tate duality and sequence.
- J. W. S. Cassels, "Arithmetic on curves of genus 1. IV. Proof of the Hauptvermutung", J. Reine Angew. Math. 211
  (1962), 95–112, for elliptic curves; and J. Tate, "Duality theorems in Galois cohomology over number fields", Proc.
  Internat. Congr. Mathematicians (Stockholm, 1962), for abelian varieties, as cited by Milne and by Poonen–Stoll.
- B. Poonen and M. Stoll, *The Cassels-Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999),
  1109–1149, doi:10.2307/121064: Introduction, pp. 1110–1111 (the statement).
