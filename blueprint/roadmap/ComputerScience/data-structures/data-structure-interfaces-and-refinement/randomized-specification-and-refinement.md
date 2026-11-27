# Randomized state-transition specification and distributional refinement

A *randomized specification* assigns to each state $s$ and operation $o$ a probability distribution $\mathsf{law}(s, o)$ on pairs (next state, result); its support is a relational state-transition specification. A client runs against it by sampling each operation's outcome, which yields a joint distribution of the client's final result and final state.

A *distributional refinement* of a randomized specification $D$ by an implementation that may flip fair coins is a refinement (invariant $I$, abstraction $\alpha$) of the supports in which, from every state $e$ with $I(e)$, each admissible method's joint law of (result, $\alpha$(final state)) equals $\mathsf{law}(\alpha(e), o)$. A resamplable hash family is the special case whose state is a seed, whose `resample` operation draws a fresh seed, and whose `eval`$(u)$ operation returns the hash value at $u$.

## Depends on

- [State-transition specification of a data structure](state-transition-specification.md)
- [Refinement of a data-structure specification by an abstraction function](refinement-by-abstraction-function.md)

## Sources

- M. Mitzenmacher and E. Upfal, "Probability and Computing", 2nd edition, Cambridge University Press, 2017.
