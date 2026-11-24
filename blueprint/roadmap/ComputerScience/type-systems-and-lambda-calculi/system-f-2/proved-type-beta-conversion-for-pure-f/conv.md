# Type-beta conversion in Fω

Type β-conversion $A \equiv_\beta B$ between [type
operators](../intrinsically-kinded-type-operators-for-pure-f/ty.md) $A, B \in
\mathrm{Ty}^{\kappa}_{\Delta}$ of the same kind over the same kinding context is the least relation
closed under the following rules: reflexivity, symmetry and transitivity; the β-rule $(\lambda B)\,A
\equiv_\beta B[A]$ for $B \in \mathrm{Ty}^{\mu}_{\kappa \cdot \Delta}$ and $A \in
\mathrm{Ty}^{\kappa}_{\Delta}$
([instantiation](../intrinsically-kinded-type-operators-for-pure-f/instantiate.md)); and
compatibility with every constructor: if $B \equiv_\beta C$ then $\lambda B \equiv_\beta \lambda C$
and $\forall_\kappa B \equiv_\beta \forall_\kappa C$; if $F \equiv_\beta G$ and $A \equiv_\beta B$
then $F\,A \equiv_\beta G\,B$; if $A \equiv_\beta A'$ and $B \equiv_\beta B'$ then $A \to B
\equiv_\beta A' \to B'$.
