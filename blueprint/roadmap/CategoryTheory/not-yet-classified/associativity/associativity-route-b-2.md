# Associativity Route B

Route B: apply outer substitution, then flat inner substitution, then relabel.

1. `tensor.map` flattenA-to-flattenB hom
2. `flattenIso.hom.app groupingB`
3. `tensor.map` of family hom with `gamma` at none and `singletonIso` at some
4. `gamma.app innerData`
5. `O.relabelIso totalIso`
