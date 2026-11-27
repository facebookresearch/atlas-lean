# The Chinese Wall model

Let $S$ be a set of subjects and $O$ a set of objects. Each object $o$ carries a security label $(X(o), Y(o))$, where $X(o)$ is its *conflict of interest class* and
$Y(o)$ its *company dataset*; write $x_j = X(o_j)$ and $y_j = Y(o_j)$. The model is given by the following axioms and definition.

- (Axiom 1) $y_1 = y_2 \implies x_1 = x_2$: objects of the same company dataset belong to the same conflict of interest class.
- (Definition 1) $N$ is a Boolean matrix indexed by $S \times O$, with $N(v, c)$ true exactly when subject $s_v$ has, or has had, access to object $o_c$. When a request
  $R(u, r)$ by $s_u$ for a new object $o_r$ is granted, $N(u, r)$ is set to true, so every request causes a transition from $N$ to some $N'$.
- (Axiom 2, simple security) Access to an object $o_r$ by a subject $s_u$ is granted if and only if for every $c$ with $N(u, c)$ true, $x_c \ne x_r$ or $y_c = y_r$.
- (Axiom 3) $N(v, c)$ false for all $(v, c)$ is an initially secure state.
- (Axiom 4) If $N(u, c)$ is false for every $c$, then any request $R(u, r)$ is granted.

Thus a subject may access objects of a conflict of interest class freely until it first accesses one of them, after which it is confined in that class to the
company dataset it chose.

## Sources

- D. F. C. Brewer and M. J. Nash, "The Chinese Wall security policy", *Proceedings of the 1989 IEEE Symposium on Security and Privacy*, pp. 206–214, copy at <https://cgi.cse.unsw.edu.au/~meyden/3441/brewernash.pdf>: Annex A, "Basic model" (Axioms 1–4, Corollary 1 and Definition 1), p. 212.
