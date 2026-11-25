# Tensor Hom apply heq

Heterogeneous congruence for a graded tensor-map component.

Rewrite direction: after a complex tensor component has been rewritten to
`GradedObject.Monoidal.tensorHom`, use this lemma to replace the two input
graded maps by `HEq`-equal shallow maps without unfolding the tensor object.
`GradedTensorTowerTests` contains a direct heterogeneous client.
