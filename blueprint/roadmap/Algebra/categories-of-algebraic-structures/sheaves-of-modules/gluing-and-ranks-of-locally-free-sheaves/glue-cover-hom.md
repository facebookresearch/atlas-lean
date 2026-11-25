# Glue Cover Hom

The glued presheaf morphism: bundle the glued values (additive and
linear by `gluedApp_add`/`gluedApp_smul`) with naturality
(`gluedApp_natural`, via `Subsingleton.elim` since opens maps are unique).
A morphism of sheaves of modules is a morphism of underlying presheaves,
so this already determines the sheaf morphism.
