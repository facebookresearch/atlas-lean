# Relative-frequency PCFG estimates are tight

Let $G$ be a context-free grammar with start symbol $S$ and let a treebank be a nonempty finite
multiset of finite parse trees of $G$ rooted at $S$. For each nonterminal $A$ that occurs in the treebank,
set the probability of a production $A \to \alpha$ to its number of occurrences divided by the total
number of occurrences of productions with left side $A$; productions of nonterminals that do not occur
are dropped (or given any probabilities, which does not affect the result). The resulting PCFG,
restricted to the nonterminals that occur, is tight: the probabilities of its finite derivations from
$S$ sum to $1$.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Probabilistic context-free grammars and tightness.

## Sources

- Z. Chi and S. Geman, *Estimation of probabilistic context-free grammars*, Computational Linguistics 24(2) (1998) 299–305: the relative-frequency (maximum-likelihood) estimator from a sample of finite parse trees (Section 2, Eq. (3)) and the Theorem of Section 3 that it is tight, null and unit productions allowed. <https://aclanthology.org/J98-2005.pdf>
