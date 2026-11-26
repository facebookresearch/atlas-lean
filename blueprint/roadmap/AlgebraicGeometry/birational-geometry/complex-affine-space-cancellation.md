# An explicit failure of complex affine-space cancellation

In $P=\mathbb C[p,s,u,F,J]$ put $x=s^2+u^3+p^2F$ and $H=x^2F-(1+2sx)J-p^2J^2-pu$. The algebra $A=P/(H)$ is a finite-type complex domain of Krull dimension four. Its one-variable polynomial algebra $A[w]$ is isomorphic as a complex algebra to a five-variable polynomial ring, but $A$ is not isomorphic as a complex algebra to a four-variable polynomial ring.

## Depends on

- Principal ideal quotient of the specified polynomial ring, finite type and Krull dimension.

## Proof depends on

- Stable trivialization of the explicit hypersurface and the equivariant-lift obstruction to polynomiality.

## Expansion

Check the defining polynomial and the domain/dimension calculations separately. Then give inverse polynomial maps after adjoining the variable, and prove the obstruction to any four-coordinate system using the Rees-invariant and polynomial-torsor lift.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ComplexCancellation.lean#L25-L27) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ComplexCancellation.lean).
