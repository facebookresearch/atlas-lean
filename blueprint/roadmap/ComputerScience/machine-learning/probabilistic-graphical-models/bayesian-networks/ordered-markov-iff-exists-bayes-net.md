# The ordered Markov property is equivalent to factorization

**The ordered Markov property is equivalent to factorization** (Lauritzen 2009): let $\alpha$ be
a finite nonempty type and $P : \alpha^n \to \mathbb{R}$ a probability distribution. Then $P$ has
the ordered Markov property for parent sets $\mathrm{pa}(k) \subseteq \{0, \dots, k-1\}$ if and
only if it is the joint distribution of a Bayesian network with these parent sets.

For the parent sets of a DAG listed in a topological order, a joint law encodes the
independencies "each variable depends on its predecessors only through its parents" exactly when it
factorizes as $\prod_k P(x_k \mid x_{\mathrm{pa}(k)})$ (Pearl 1995, eq. (2)).
