---
article_id: af_f330bc0788ddb9f1acae2c99
declaration: def
origin: cited
statement: formalized
lean: ChainHomotopy.HomotopicChainMaps
---

# Definition 23.51

Two morphisms $f, g: C \rightarrow D$ of chain complexes are homotopic if there exist morphisms $h_{n}: C_{n} \rightarrow D_{n+1}$ such that $f_{n}-g_{n}=d_{n} \circ h_{n}+h_{n-1} \circ d_{n-1}$ for all $n \geq 0$ (where $h_{-1}\coloneqq 0$); this defines an equivalence relation $f \sim g$, since (a) $f \sim f$ (take $h=0$), (b) if $f \sim g$ via $h$ then $g \sim f$ via $-h$, and (c) if $f_{1} \sim f_{2}$ via $h_{1}$ and $f_{2} \sim f_{3}$ via $h_{2}$ then $f_{1} \sim f_{3}$ via $h_{1}+h_{2}$.

## Depends on

- [Definition 23.49](489-definition-23-49.md)

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 23.7, Subsection 23.7.1](../../../../../../sources/v1/NumberTheoryI.md)
