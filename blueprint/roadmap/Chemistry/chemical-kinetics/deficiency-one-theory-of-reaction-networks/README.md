# Deficiency-one theory of reaction networks

Feinberg's deficiency-one theorem concerns a mass-action system with finitely many species and
reactions in which (1) every linkage class `θ` has deficiency `δ_θ ≤ 1`, (2) the linkage-class
deficiencies sum to the deficiency of the network, `∑_θ δ_θ = δ`, and (3) each linkage class
contains exactly one terminal strong linkage class (a maximal set of complexes mutually reachable
along directed reaction paths, out of which no reaction leads). For every choice of positive rate
constants, each positive stoichiometric compatibility class then contains at most one positive
equilibrium, and exactly one if the network is weakly reversible.

These pages cover the linear algebra of condition (2). For finitely many species and reactions, the
linkage-class deficiencies always sum to at most `δ`, with equality exactly when the stoichiometric
subspaces of the linkage classes are independent; the equilibrium equations then decouple across
linkage classes, for all real rate constants and concentrations.

## Objects attached to a linkage class

- [Linkage class of a reaction](linkage-class-of.md)
- [Reaction network of a linkage class](linkage-class-network.md)
- [Stoichiometric subspace of a linkage class](linkage-class-stoichiometric-subspace.md)
- [Deficiency of a linkage class](linkage-class-deficiency.md)
- [Mass-action field of a linkage class](linkage-class-field.md)

## Reactions and linkage classes

- [The product complex of a reaction lies in its linkage class](linkage-class-of-prod.md)
- [Reactions with source complex in a linkage class belong to it](linkage-class-of-eq-of-src-mem.md)
- [Reactions with product complex in a linkage class belong to it](linkage-class-of-eq-of-prod-mem.md)

## Stoichiometric subspaces of linkage classes

- [Reaction vectors of a linkage class lie in its stoichiometric subspace](reaction-vector-mem-linkage-class-stoich.md)
- [The stoichiometric subspace is the sum of the linkage-class subspaces](stoichiometric-subspace-eq-i-sup.md)

## Dimension of the stoichiometric subspace

- [The stoichiometric dimension is at most the sum over linkage classes](finrank-stoichiometric-subspace-le-sum.md)
- [s = ∑ s_θ iff the linkage-class subspaces are independent](finrank-stoichiometric-subspace-eq-sum-i.md)

## Linkage-class deficiencies

- [The number of complexes is the sum of the linkage-class sizes](card-complexes-eq-sum.md)
- [Each linkage class has nonnegative deficiency](linkage-class-deficiency-nonneg.md)
- [Deficiency minus the sum of the linkage-class deficiencies](deficiency-sub-sum-linkage-class-deficie.md)
- [The linkage-class deficiencies sum to at most the deficiency](sum-linkage-class-deficiency-le.md)
- [∑ δ_θ = δ iff the linkage-class subspaces are independent](sum-linkage-class-deficiency-eq-iff.md)
- [Each linkage-class deficiency is at most the network deficiency](linkage-class-deficiency-le-deficiency.md)
- [In a deficiency-zero network every linkage class has deficiency zero](linkage-class-deficiency-eq-zero-of-defi.md)
- [In a deficiency-zero network the linkage-class deficiencies sum to δ](sum-linkage-class-deficiency-eq-of-defic.md)

## Decoupling of the equilibrium equations

- [The mass-action field is the sum of the linkage-class fields](sum-linkage-class-field.md)
- [Each linkage-class field takes values in its stoichiometric subspace](linkage-class-field-mem.md)
- [The equilibrium equations decouple across independent linkage classes](mass-action-field-eq-zero-iff-of-i-sup-i.md)
- [Under ∑ δ_θ = δ the equilibrium equations decouple by linkage class](mass-action-field-eq-zero-iff-of-sum-lin.md)

## Related topics

- [Complex balancing and the deficiency-zero theorem](../../../Biology/systems-biology/complex-balancing-and-the-deficiency-zero-theore/README.md): linkage classes and the deficiency-zero theorem: for a weakly reversible network of deficiency zero with finitely many species and reactions, every choice of positive rate constants gives exactly one positive equilibrium in each positive stoichiometric compatibility class.
