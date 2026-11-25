# Associator hom f eq graded

A complex associator component is the graded-carrier associator component.

Rewrite direction: from `HomologicalComplex.associator … .hom.f j` to the
graded-object associator at `j`.  The contract test then changes carriers
with `GradedObject.Monoidal.associator_hom_apply_heq`.
