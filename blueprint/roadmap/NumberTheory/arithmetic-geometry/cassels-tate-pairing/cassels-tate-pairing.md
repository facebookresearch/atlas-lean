# Cassels' pairing on the Shafarevich–Tate group of an elliptic curve

Let $E$ be an
elliptic curve over a number field $K$, and let $\text{Ш}(E)$ be its Shafarevich–Tate group.
There is a biadditive pairing
$\langle\,,\rangle \colon \text{Ш}(E) \times \text{Ш}(E) \to \mathbb{Q}/\mathbb{Z}$ that is
alternating, $\langle x, x\rangle = 0$ for all $x$, and that becomes nondegenerate after one
divides $\text{Ш}(E)$ by its maximal divisible subgroup: an element $x$ satisfies
$\langle x, y\rangle = 0$ for all $y$ if and only if $x$ lies in a divisible subgroup of
$\text{Ш}(E)$.

The divisible subgroups generate a divisible subgroup, so an element lies in some divisible
subgroup exactly when it lies in the maximal divisible subgroup. The kernel on the other side is
the same, since an alternating pairing is antisymmetric. The statement asserts that such a
pairing exists; it does not single out the pairing Cassels constructs.

## Informally uses

- [The principal polarization of an elliptic curve](../../../AlgebraicGeometry/elliptic-curves/principal-polarization-of-an-elliptic-curve.md), for the isomorphism $\varphi_L \colon E \to E^\vee$ of the divisor $(O)$, through which the pairing on $\text{Ш}(E)$ is $(x, y) \mapsto \langle x, \varphi_L(y) \rangle$
- [The Cassels–Tate pairing of an abelian variety](construction-of-the-cassels-tate-pairing/cassels-tate-pairing-of-an-abelian-variety.md), for the pairing $\text{Ш}(E) \times \text{Ш}(E^\vee) \to \mathbb{Q}/\mathbb{Z}$
- [Nondegeneracy of the Cassels–Tate pairing](proof-of-the-nondegeneracy-of-the-cassels-tate-pairing/nondegeneracy-of-the-cassels-tate-pairing.md), for the kernels, carried to $\text{Ш}(E)$ by the isomorphism $\varphi_L$
- [The Cassels–Tate pairing is alternating for a polarization coming from a line bundle](alternating-property-of-the-cassels-tate-pairing.md), applied to the $K$-rational divisor $D = (O)$, for $\langle x, \varphi_L(x) \rangle = 0$

## Sources

- B. Poonen and M. Stoll, *The Cassels-Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999), 1109–1149, doi:10.2307/121064, Introduction, p. 1110, stating the theorem of J. W. S. Cassels, *Arithmetic on curves of genus 1. IV. Proof of the Hauptvermutung*, J. Reine Angew. Math. 211 (1962), 95–112. See also J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed. (2006), Theorem I.6.13 (a), p. 82, for the kernels, and p. 81 for the alternating property.
