# One-sample matroid selection against an almighty adversary

For every $n\ge0$ and matroid on the full labelled ground set $[n]$, there are a finite bit-string seed space, a probability law on it, and a measurable online rule, all fixed by the matroid. At each arrival the rule sees the seed, the full sample vector, and the labelled value prefix through that arrival; its Boolean decision is irrevocable. For every seed, every nonnegative sample and value vector, every arrival permutation, and every prefix, the accepted set is independent.

On any probability space let $(S_e,V_e)_{e\in[n]}$ be jointly independent as $2n$ coordinates, nonnegative almost surely, with $S_e$ and $V_e$ identically distributed for each $e$. Let the seed be independent of the pair of vectors and have the prescribed law. All vector and seed maps are measurable. Let $\mathrm{OPT}(V)=\max_{J\text{ independent}}\sum_{e\in J}V_e$, and assume only that this offline optimum is integrable. For every measurable arrival permutation (even one depending on both full vectors and the seed), the sum of accepted online values is integrable and has expectation at least $2^{-310}\mathbb E\mathrm{OPT}(V)$.

**Conventions.** Use the full-ground finite matroid model, inclusive-prefix decisions, and explicitly typed seed and sample laws and the measurable adversarial arrival map as above. A single-threshold prophet inequality for known distributions does not provide this fixed sample-only rule.

## Depends on

- [Irrevocable matroid prefix rules](online-matroid-prefix-rule.md)

## Proof depends on

- [Hidden-vector matroid selection against worst order](hidden-vector-matroid-selection.md)

## Expansion

Construct the exchangeable paired-sample reduction with independent seed. Prove the transferred decisions depend only on the observed sample and actual prefix and preserve independence for every prefix. Derive integrability by domination by the offline optimum, not by separately requiring integrability of every label (loops need not contribute).

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MatroidProphet.lean#L89-L91)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/111.md)
- [Accompanying manuscript: One Sample Suffices for Matroid Prophet Inequalities against an Almighty Adversary](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/One-Sample-Suffices-for-Matroid-Prophet-Inequalities-against-an-Almighty-Adversary-September-23-2026/final.pdf)
- [Pinned additional source formulation](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MatroidSecretary.lean#L235-L237)
