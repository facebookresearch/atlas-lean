# Lower dimension for equal positive contractions without exact overlaps

For a nonempty finite family $f_i(x)=\lambda x+t_i$ with $0<\lambda<1$ and positive weights $p_i$ summing to one, suppose the map from every finite word (including the empty word) to its composed affine map is injective. If the Borel probability measure $\mu$ satisfies $\mu=\sum_i p_i(f_i)_*\mu$, then its lower Hausdorff dimension, the infimum over measurable positive-$\mu$ sets, is $\min(1,[-\sum_i p_i\log p_i]/\log(1/\lambda))$ with natural logarithms.

## Depends on
The probability, composition, and lower-dimension conventions of the general entropy-rate statement.

## Proof depends on
- [Entropy-rate formula](entropy-rate-dimension-self-similar-measures.md).

## Proof strategy
Use injectivity of the word-to-map assignment to identify each mass with one product and reduce $n$-step entropy to $n$ times the symbol entropy. Normalize both sides from base two to natural logarithms.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SelfSimilarCorollaries.lean#L49-L56) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/148.md).
