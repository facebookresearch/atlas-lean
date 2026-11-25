# Algebra Enrichment

The actual one-object cochain enrichment of a DG algebra. Composition is the product in the
native order, `a ≫ b = a * b`. Consequently a DG presheaf on this category (for instance a
`DGQuasiFunctorModels.RightModule`) satisfies `M (a * b) = M a ∘ M b`: it is a *left* `A`-module.
Conventional right `A`-modules are presheaves on the category of the opposite DG algebra (with the
Koszul sign on homogeneous elements).
