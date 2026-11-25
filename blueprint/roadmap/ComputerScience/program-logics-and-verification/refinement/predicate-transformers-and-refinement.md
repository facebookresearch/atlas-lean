# Predicate transformers and refinement

Let $\Sigma$ be a state space and $\mathcal{P} = 2^\Sigma$ the predicates on it, ordered by inclusion. A *predicate transformer* is a monotone
function $S : \mathcal{P} \to \mathcal{P}$. Arbitrary monotone transformers may be *miraculous*, with $S(\emptyset) \ne \emptyset$, as refinement calculi allow. A *strict* transformer, one with $S(\emptyset) = \emptyset$, is read as a weakest precondition: $S(Q)$ is the set of initial states from which $S$ is guaranteed to
terminate in a state of $Q$.

- *Refinement*: $S \sqsubseteq T$ if $S(Q) \subseteq T(Q)$ for every $Q \in \mathcal{P}$.
- *Sequential composition* $(S ; T)(Q) = S(T(Q))$, *demonic choice* $(S \sqcap T)(Q) = S(Q) \cap T(Q)$ and *angelic choice*
  $(S \sqcup T)(Q) = S(Q) \cup T(Q)$; meets and joins of arbitrary families are taken pointwise in the same way.
- *Total correctness*: $S$ satisfies the triple $[P]\, S\, [Q]$ if $P \subseteq S(Q)$.
- The *specification statement* $[P, Q]$ is the transformer mapping $R$ to $P$ if $Q \subseteq R$ and to $\emptyset$ otherwise. For a monotone $T$,
  $[P, Q] \sqsubseteq T$ exactly when $P \subseteq T(Q)$, that is, when $T$ satisfies $[P]\, T\, [Q]$. With $Q = \emptyset$ and $P$ nonempty, $[P, Q]$ is miraculous.

## Expansion

Fix a programming language with a total-correctness weakest-precondition semantics $\mathrm{wp}(c)$, so that refinement between programs and
specification statements is stated for programs rather than for arbitrary transformers. Check the definitions against an opened source with a
precise locator.

## Sources

- R.-J. Back and J. von Wright, *Refinement Calculus: A Systematic Introduction*, Springer, 1998.
- C. Morgan, *Programming from Specifications*, 2nd ed., Prentice Hall, 1994.
