# Independent commuting derivations with a coordinate-free joint kernel

In $\mathbb C[h,u,v,w]$ set $x=u^3+hv$, $y=-u^2+hw$, $s=2u^3v+3u^4w+h(v^2-3u^2w^2)+h^2w^3$, and $F=h+2s^2x-3sy^2+3s^3y-1$. For $n\ge4$ regard these as polynomials in the first four coordinates of $A=\mathbb C[X_0,\ldots,X_{n-1}]$.

There are $n-1$ complex derivations of $A$ into itself that kill $F+1$, commute pairwise on every polynomial, and are linearly independent over $A$. Each is locally nilpotent: for every polynomial some nonnegative iterate gives zero. Their joint kernel is exactly $\mathbb C[F]$, and no polynomial in that kernel is the image of a coordinate under any complex polynomial automorphism of $A$. With derivation indices ordered as three core indices followed by the extras, derivation $3+i$ is $\partial/\partial X_{4+i}$ for $0\le i<n-4$.

## Depends on

- Polynomial derivations, kernels, adjoining a single polynomial, stable variable inclusions.

## Proof depends on

- Commuting locally nilpotent core derivations, their exact invariant ring, and the noncoordinate theorem for every invariant.

## Expansion

Construct and check the three core derivations, their commutators and the joint invariant calculation; use ordinary partial derivatives on the extra block and show independence and exact kernel persist.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CommutingDerivations.lean#L54-L68) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CommutingDerivations.lean).
