# Finite iteration computes the least fixed point

Let $\alpha$ be a finite type with
$|\alpha|$ elements, let $f$ be a map from subsets of $\alpha$ to subsets of $\alpha$ that is
monotone for inclusion, and let $\mathrm{lfp}_{\mathrm{fin}}(f) = f^{|\alpha|}(\emptyset)$ be the
result of applying $f$ to $\emptyset$ $|\alpha|$ times. Let $F$ be a map from predicates on $\alpha$
to predicates on $\alpha$ that is monotone for the pointwise order. For $Z \subseteq \alpha$
write $P_Z$ for the predicate $t \mapsto t \in Z$, and suppose that for every $Z \subseteq \alpha$
and every $s \in \alpha$, $s \in f(Z)$ if and only if $F(P_Z)(s)$ holds. Then for every
$s \in \alpha$, $s \in \mathrm{lfp}_{\mathrm{fin}}(f)$ if and only if $s$ satisfies the least
fixed point of $F$ in the complete lattice of predicates on $\alpha$.

One inclusion is iteration into the fixed point; the other is Park induction: the
$|\alpha|$-th iterate of $F$ from the everywhere-false predicate is pre-fixed because the
corresponding iterate of $f$ has stabilized, transported through the hypothesis relating $f$
and $F$.
