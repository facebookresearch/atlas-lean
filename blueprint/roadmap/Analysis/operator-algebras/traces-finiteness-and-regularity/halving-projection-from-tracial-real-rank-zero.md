# A uniform trace-halving projection from tracial real rank zero

Let $A$ be a nonzero, separable, simple, unital, infinite-dimensional, nuclear, stably finite complex $C^*$-algebra with a nonempty tracial state space. Simplicity concerns closed two-sided ideals; stable finiteness means every matrix isometry is unitary. The comparator expresses nuclearity by uniqueness (at most one) of the $C^*$-norm on algebraic tensors with each unital complex $C^*$-algebra in a fixed test universe. The comparator’s $A$ is in the small universe `Type`, while the entire assertion is parameterized by the test universe. Form $D$ from operator-norm-bounded sequences in $A$ Cauchy in $\|a\|_{2,u}=\sup_\tau\tau(a^*a)^{1/2}$, modulo the ordinary $\|\cdot\|_{2,u}$-null ideal. Each trace of $A$ induces a trace of $D$ by ordinary limit. For a free ultrafilter $\omega$ on $\mathbb N$, form the quotient $D_\omega$ of bounded sequences in $D$ by those tending to zero in the induced uniform two-norm along $\omega$.

Assume $D_\omega$ has real rank zero, meaning that every self-adjoint element admits arbitrary norm approximations by self-adjoint elements of finite complex spectrum. Then there is a self-adjoint projection $p\in D_\omega$ commuting with the constant image of every $x\in D$ such that for every sequence $(\tau_n)$ of tracial states of $A$, its induced ultralimit trace $\lambda$ satisfies $\lambda(px)=\lambda(x)/2$ on all constant images $x$. The real-rank-zero premise is on this specified ultrapower and the claim uses its specified family of limit traces.

## Depends on
Quotient $C^*$-norm, two-norm-null closed star ideal, uniform Cauchy subalgebra, and limit traces descending through the null ideal. The source asserts existence of the law bundles supplying all these constructions, not a result conditional on opaque construction classes.

## Proof depends on
The five law packages for the quotient norm, null ideal, Cauchy subalgebra, limit and descended trace; then a trace-halving projection construction using the real-rank-zero approximations.

## Expansion
Implement those law packages before stating the projection theorem on the actual two-stage quotient. Verify limit trace existence and descent for every trace sequence and obtain centrality relative to the completion. No conclusion about an arbitrary group action, strict comparison, or Jiang–Su absorption is included here.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/UniformGamma.lean#L600-L602) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/291.md).
