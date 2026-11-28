# The finitely presented simple version of the Boone–Higman equivalence

A finitely generated group has decidable word problem if and only if it embeds by an injective group homomorphism into a group that is both finitely presented and simple. Decidable word problem means that for some finite generating tuple, membership in the identity language of finite words in that tuple and its formal inverses is computable. The ambient group itself is simple, not merely a finitely presented overgroup of a simple intermediate subgroup.

## Depends on

- Finite presentations, injective homomorphisms and computable signed-word evaluation.

## Proof depends on

- [Classical easy direction](boone-higman-embedding.md), and a construction of a single finitely presented simple overgroup from a decidable word problem.

## Expansion

Identify the signed-word computational model with decision on reduced free words. For the easy implication use the ambient simple group as the simple intermediate group. For the reverse implication verify the finite presentation and simplicity of the same target.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BooneHigman.lean#L26-L29) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BooneHigman.lean).
