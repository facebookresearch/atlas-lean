# A degree-five stable noncoordinate with nonrectifiable affine-space fibers

Put $Q=X_1^2-X_3^2+X_0X_2$ and $f=X_0-2Q\bigl(Q(X_1+X_3)+X_0X_3\bigr)$ in $R=\mathbb C[X_0,X_1,X_2,X_3]$. Its total degree is five. In $R[X_4]$ some complex polynomial automorphism sends $f$ to $X_0$, but none in $R$ does. For every $t\in\mathbb C$, the quotient $R/(f-t)$ is isomorphic to the complex polynomial ring on three variables, while no complex automorphism of $R$ maps the ideal $(f-t)$ to $(X_0)$. The two fiber assertions use the same $f$ and hold also at $t=0$.

## Depends on

- Stabilization by one ordinary variable, quotient by a principal ideal, and ideal transport under automorphisms.

## Proof depends on

- Explicit stable automorphism, individual affine-fiber isomorphisms and their ambient nonrectifiability.

## Expansion

Check degree from the displayed formula. Track the specialized fiber isomorphisms including the zero fiber; prove nonrectifiability as an ideal-level obstruction, not merely a failure of a proposed coordinate change.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/StableCoordinateFour.lean#L48-L51) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/StableCoordinateFour.lean).
