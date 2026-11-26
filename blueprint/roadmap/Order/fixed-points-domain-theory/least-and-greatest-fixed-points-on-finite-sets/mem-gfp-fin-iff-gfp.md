# Finite iteration computes the greatest fixed point

Let $\alpha$ be a finite type with
$|\alpha|$ elements, let $f$ be a map from subsets of $\alpha$ to subsets of $\alpha$ that is
monotone for inclusion, and let $\mathrm{gfp}_{\mathrm{fin}}(f) = f^{|\alpha|}(\alpha)$ be the
result of applying $f$ to $\alpha$ $|\alpha|$ times. Let $F$ be a map from predicates on $\alpha$
to predicates on $\alpha$ that is monotone for the pointwise order. For $Z \subseteq \alpha$
write $P_Z$ for the predicate $t \mapsto t \in Z$, and suppose that for every $Z \subseteq \alpha$
and every $s \in \alpha$, $s \in f(Z)$ if and only if $F(P_Z)(s)$ holds. Then for every
$s \in \alpha$, $s \in \mathrm{gfp}_{\mathrm{fin}}(f)$ if and only if $s$ satisfies the greatest
fixed point of $F$ in the complete lattice of predicates on $\alpha$.

This is dual to the corresponding statement for least fixed points.
