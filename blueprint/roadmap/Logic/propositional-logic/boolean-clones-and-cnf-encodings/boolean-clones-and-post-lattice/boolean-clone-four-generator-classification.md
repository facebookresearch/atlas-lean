# Every Boolean clone is essentially unary or contains AND, OR, majority or minority

Let $C$ be a positive-arity Boolean clone. Then either every operation of $C$ is essentially unary, or $C$ contains at least one of the four operations $\wedge$, $\vee$, $\mathrm{maj}$, $x \oplus y \oplus z$. This is the algebraic core shared by Post's criterion and Schaefer's dichotomy.

## Proof sketch

Take $f \in C$ not essentially unary and let $\hat f(x) = f(x,\dots,x)$. If $\hat f$ is constant, say $0$, a binary minor $g$ of $f$ has $g(0,0) = g(1,1) = 0$ and $g(1,0) = 1$; then $g$ is exclusive or, which gives minority as $g(x, g(y,z))$, or else $x \wedge y = g(x, g(x,y))$ (dually for the constant $1$). If $\hat f = \neg$, then $\hat f \circ f$ is idempotent and not a projection. Take an idempotent non-projection $g \in C$ of least arity $m$. For $m = 2$, $g$ is $\wedge$ or $\vee$. For $m = 3$, every identification of two arguments is a projection; of the eight resulting patterns, one is majority, one is minority, three would make $g$ a projection, and the remaining three generate majority (e.g. $\mathrm{maj}(x,y,z) = g(x, g(x,y,z), z)$). The case $m \ge 4$ is impossible: identifications force $g$ to be a projection.

## Depends on

- [Essentially unary operations](essentially-unary-operations.md)
- [Boolean clones](boolean-clones.md)

## Sources

- H. Chen, "A Rendezvous of Logic, Complexity, and Algebra", SIGACT News 37(4), 85–114, 2006 (extended version ACM Computing Surveys 42(1), 2009): Theorem 5.1 and its proof.
- E. L. Post, The Two-Valued Iterative Systems of Mathematical Logic, Annals of Mathematics Studies 5, Princeton University Press, 1941.
