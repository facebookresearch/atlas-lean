# Nondegeneracy of the Cassels–Tate pairing

This is the theorem of Cassels and Tate that the kernels of the
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

Proof, following Milne. The pairing kills the divisible subgroups. Fix $m$; the left kernel of the pairing between
the $m$-primary parts is $\text{Ш}(K, A)(m)_{\mathrm{div}}$, by local duality, the Poitou–Tate sequence and the key lemma,
through a finite set $S$ of places containing the archimedean places, the places of bad reduction and those above the
primes dividing $m$; and the right kernel is $\text{Ш}(K, A^\vee)(m)_{\mathrm{div}}$, by comparing the finite orders of the
quotients for $A$, $A^\vee$ and $A^{\vee\vee} \cong A$; see
[Proof of the nondegeneracy of the Cassels–Tate pairing](proof-of-the-nondegeneracy-of-the-cassels-tate-pairing/README.md).

For elliptic curves and $m$ prime, $\text{Ш}^2_S(K, A_m) = 0$, so every element of $\text{Ш}(K, A)[m]$ becomes divisible by $m$
over $G_S$ and the argument is shorter (Milne, Remark I.6.18).

Milne builds the pairing from the $e_m$-pairing of the Cartier duality of $A[m]$ and $A^\vee[m]$, while the
[construction page](cassels-tate-pairing-of-an-abelian-variety.md) uses the Weil pairing as Poonen and Stoll define it; the
two [agree up to sign](construction-of-the-cassels-tate-pairing/weil-pairing-and-cartier-duality.md), and a change of sign of $e_m$ changes the pairing by a sign, which does not change its kernels.

## Depends on

- [The Cassels–Tate pairing of an abelian variety](cassels-tate-pairing-of-an-abelian-variety.md)

## Proof depends on

- [The Cassels–Tate pairing kills the divisible subgroups](proof-of-the-nondegeneracy-of-the-cassels-tate-pairing/cassels-tate-pairing-kills-divisible-subgroups.md)
- [The left kernel of the Cassels–Tate pairing is the divisible subgroup](proof-of-the-nondegeneracy-of-the-cassels-tate-pairing/left-kernel-of-the-cassels-tate-pairing.md)
- [The right kernel of the Cassels–Tate pairing is the divisible subgroup](proof-of-the-nondegeneracy-of-the-cassels-tate-pairing/right-kernel-of-the-cassels-tate-pairing.md)
- [Selmer groups and the torsion of the Shafarevich–Tate group of an abelian variety](selmer-groups-of-abelian-varieties.md), for the finiteness of $\text{Ш}(K, A)(\ell)$ modulo its divisible subgroup (its item 3), used to pass between the primary components and the whole groups

## Sources

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, Theorem 6.13 (a) (p. 82: "The left and right kernels of the canonical pairing
  $\text{Ш}^1(K, A)(m) \times \text{Ш}^1(K, A^t)(m) \to \mathbb{Q}/\mathbb{Z}$ are the divisible subgroups"), its proof through
  Lemmas 6.15–6.17 (pp. 86–89), Remark 6.18 (p. 89), and the Notes (p. 93: proved by Cassels for elliptic curves and by
  Tate in general); Theorem 6.26 (a) (p. 92), which restates Theorem 6.13 (a); Theorem 4.10 (pp. 56–57) for the
  Poitou–Tate duality and sequence.
- J. W. S. Cassels, "Arithmetic on curves of genus 1. IV. Proof of the Hauptvermutung", J. Reine Angew. Math. 211
  (1962), 95–112, for elliptic curves; and J. Tate, "Duality theorems in Galois cohomology over number fields", Proc.
  Internat. Congr. Mathematicians (Stockholm, 1962), for abelian varieties, as cited by Milne, Notes to Chapter I, §6,
  p. 93, and by Poonen and Stoll, Introduction, p. 1110; not read.
- B. Poonen and M. Stoll, *The Cassels-Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999),
  1109–1149, doi:10.2307/121064: Introduction, pp. 1110–1111 (the statement).
