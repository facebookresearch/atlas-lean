# Waldhausen Category

Standard Waldhausen structure on a Quillen exact category.

Cofibrations are the admissible monomorphisms and weak equivalences are the
isomorphisms. This is the canonical bridge from exact categories to Waldhausen
categories.

Use locally as `letI := ExactCategory.waldhausenCategory C`; no global
`WaldhausenCategoryWithoutGluing C` instance is installed so that other Waldhausen
structures on the same underlying category (e.g. chain complexes) remain
available.
