# Individual proper infiniteness gives full two-corner diagonalization

Let $A$ be any possibly nonunital complex C*-algebra with its spectral positive order. Form the norm completion of the union of the finite C*-matrix corners under upper-left block embeddings (zero padding). Suppose that for each $h\ge0$ the $2$-by-$2$ diagonal corner with two copies of $h$ is a norm limit of $r_j^*h r_j$ in this stabilization, with $h$ on the right embedded in the one-by-one corner.

Then for all positive $a,b$, every $c\in A$ and every $\epsilon>0$ there are $s,t\in A$ with $\|s^*a s-a\|<\epsilon$, $\|t^*b t-b\|<\epsilon$ and $\|s^*ct\|<\epsilon$. In particular, for every positive $x,y$ the same conclusion holds with $a=x^2,b=y^2,c=xy$, the strong pure infiniteness clause. No exactness hypothesis is used.

## Depends on

- The upper-left matrix-corner stabilization and sequence form of Cuntz comparison.

## Proof depends on

- Diagonalization for an arbitrary off-diagonal $c$ starting from individual comparison, with estimates sufficient to put the witnesses in $A$ itself.

## Expansion

Prove agreement of the completion and standard stabilization, then isolate the cutting and approximation arguments controlling the two diagonal errors and the unrestricted off-diagonal error. Record the strong pure infiniteness conclusion by specialization.

## Sources

- OpenAI, [IndividualStrongInfiniteness comparator, individual_to_strong_main](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/IndividualStrongInfiniteness.lean#L319-L327).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/303.md).
