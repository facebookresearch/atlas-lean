# Semisimple subgroups of GL₂ over a prime field

Let $\ell$ be a prime and $\mathbb{F}_\ell = \mathbb{Z}/\ell\mathbb{Z}$. A subgroup $G$ of $\mathrm{GL}_2(\mathbb{F}_\ell)$ is
semisimple if the identity representation $G \to \mathrm{GL}_2(\mathbb{F}_\ell)$ is semisimple, that is, if every
$G$-stable line of $\mathbb{F}_\ell^2$ has a $G$-stable complement. A Cartan subgroup of $\mathrm{GL}_2(\mathbb{F}_\ell)$ is the
group of units of a commutative semisimple subalgebra of dimension $2$ of $M_2(\mathbb{F}_\ell)$: a conjugate of the
diagonal subgroup (split) or the image of $\mathbb{F}_{\ell^2}^*$ acting on $\mathbb{F}_{\ell^2} \cong \mathbb{F}_\ell^2$ (nonsplit).

Every semisimple subgroup $G$ of $\mathrm{GL}_2(\mathbb{F}_\ell)$ satisfies one of the following conditions:

1. $G$ contains $\mathrm{SL}_2(\mathbb{F}_\ell)$;
2. $G$ is contained in a Cartan subgroup $T$;
3. $G$ is contained in the normalizer of a Cartan subgroup $T$, and not in $T$;
4. the image of $G$ in $\mathrm{PGL}_2(\mathbb{F}_\ell) = \mathrm{GL}_2(\mathbb{F}_\ell)/\mathbb{F}_\ell^*$ is isomorphic to $A_4$, $S_4$ or
   $A_5$.

Deligne and Serre recall this classification from Serre's paper on the Galois properties of points of finite order on
elliptic curves for the proof of
[the bound on such subgroups with few characteristic polynomials](bounded-semisimple-subgroups-of-gl2-with-few-characteristic-polynomials.md).
The definition of a Cartan subgroup above is the usual one, which their statement leaves to that reference.

## Depends on

- [Alternating group on a finite set](../../../../GroupTheory/permutation-groups/symmetric-groups/alternating-group.md), for $A_4$ and $A_5$
- [Symmetric group: the group of permutations of a set](../../../../GroupTheory/automorphisms/automorphism-groups/symmetric-group.md), for $S_4$

## Proof depends on

- [Dickson's classification, tame case](../../../../GroupTheory/linear-groups/dickson-s-classification-of-finite-subgroups-of/classification-tame.md), for the image in $\mathrm{PGL}_2$ of a subgroup of order prime to an odd $\ell$

## Expansion

This node is still to be broken down. A good expansion states and links:

- the case of order divisible by $\ell$: a semisimple subgroup of $\mathrm{GL}_2(\mathbb{F}_\ell)$ containing an element of
  order $\ell$ contains $\mathrm{SL}_2(\mathbb{F}_\ell)$;
- the case of order prime to $\ell$, $\ell$ odd: from the tame case of Dickson's classification, applied to the image in
  $\mathrm{PGL}_2(\mathbb{F}_\ell) \subset \mathrm{PGL}_2(\overline{\mathbb{F}}_\ell)$, a cyclic image gives a subgroup of a Cartan
  subgroup, a dihedral image a subgroup of its normalizer, and the remaining images are $A_4$, $S_4$, $A_5$;
- the prime $\ell = 2$, where $\mathrm{GL}_2(\mathbb{F}_2) \cong S_3$ and each semisimple subgroup lies in a Cartan subgroup
  or is the whole group;
- the published statements (Serre [22], §2, prop. 15 and 16, as cited in Deligne–Serre (1974), p. 524).

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): §7.1, p. 523, for semisimple subgroups; the
  démonstration of Proposition 7.2, p. 524 ("Soit G un sous-groupe semi-simple de $\mathbf{GL}_2(\mathbf{F}_l)$. Rappelons
  (cf. [22] § 2, prop. 15 et 16) que l'une des conditions suivantes est satisfaite"), conditions (a)–(d).
- J.-P. Serre, *Propriétés galoisiennes des points d'ordre fini des courbes elliptiques*, Invent. Math. 15 (1972),
  259–331, §2, prop. 15 and 16, as cited in Deligne–Serre (1974), p. 524; not read.
