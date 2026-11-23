# Size of an LTL formula

The size $|\varphi|$ of an LTL formula is the number of nodes of its syntax tree: atoms and
truth count $1$, negation and next add $1$, and conjunction and until add $1$ to the sizes of
their two arguments.

Derived connectives count through their definitions in terms of the primitives: $F\varphi =
\top \mathbin{U} \varphi$ has size $|\varphi| + 2$ and $G\varphi = \neg F \neg\varphi$ has
size $|\varphi| + 4$. A bound of the form $2^{O(|\varphi|)}$ is insensitive to this choice,
because the expansion of derived connectives is linear.
