# Complete development of type-beta redexes

The complete development $A^{\circ}$ of a [type
operator](../intrinsically-kinded-type-operators-for-pure-f/ty.md) $A$ contracts all its β-redexes
at once: $\alpha_i^{\circ} = \alpha_i$, $(\lambda B)^{\circ} = \lambda B^{\circ}$, $((\lambda
B)\,A)^{\circ} = B^{\circ}[A^{\circ}]$, $(F\,A)^{\circ} = F^{\circ}\,A^{\circ}$ when $F$ is not an
abstraction, $(A \to B)^{\circ} = A^{\circ} \to B^{\circ}$ and $(\forall_\kappa B)^{\circ} =
\forall_\kappa B^{\circ}$
([instantiation](../intrinsically-kinded-type-operators-for-pure-f/instantiate.md)).
