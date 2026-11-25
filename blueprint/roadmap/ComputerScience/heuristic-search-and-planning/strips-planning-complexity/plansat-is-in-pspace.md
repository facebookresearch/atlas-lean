# PLANSAT is in PSPACE

PLANSAT, the problem of deciding whether a propositional STRIPS planning instance with condition set
$P$ has a plan, is decidable in polynomial space. A nondeterministic procedure guesses operators one at a
time, storing only the current state and a step counter bounded by $2^{|P|}$; this places PLANSAT in
NPSPACE, and Savitch's theorem gives NPSPACE $=$ PSPACE.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Proof prerequisite: STRIPS planning as search.

## Sources

- T. Bylander, *The computational complexity of propositional STRIPS planning*, Artificial Intelligence 69 (1994) 165–204, Theorem 3.1, first paragraph of the proof. <https://ai.dmi.unibas.ch/_files/teaching/hs20/po/misc/bylander-aij1994.pdf>
