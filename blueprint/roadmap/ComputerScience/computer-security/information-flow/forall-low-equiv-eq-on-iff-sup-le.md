# Joins give the level of combined information

Let security levels form a
join-semilattice $(\mathcal{L}, \sqsubseteq)$ with a least element, let
$\Gamma : V \to \mathcal{L}$ be a security policy, let $S \subseteq V$ be a finite set of
variables, and let the set $A$ of values have at least two elements. For an observer at level
$\ell$, every two stores $\sigma_1, \sigma_2 : V \to A$ with $\sigma_1 =_\ell \sigma_2$ agree on
every variable of $S$ if and only if $\bigsqcup_{x \in S} \Gamma(x) \sqsubseteq \ell$.
