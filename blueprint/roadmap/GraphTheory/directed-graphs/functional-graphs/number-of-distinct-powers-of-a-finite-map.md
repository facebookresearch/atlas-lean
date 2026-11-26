# A map on a finite set has exactly mu + lambda distinct powers

Let $f : \alpha \to \alpha$ with $\alpha$ finite, let $\mu_f$ be the largest transient depth of a state and $\lambda_f$ the least common multiple of the cycle lengths of the functional graph. For $a < b$, the iterates $f^a$ and $f^b$ are equal as functions if and only if $a \ge \mu_f$ and $\lambda_f$ divides $b - a$. Consequently $f$ has exactly $\mu_f + \lambda_f$ distinct powers $f^0, f^1, f^2, \dots$ (on the empty set $\mu_f = 0$, $\lambda_f = 1$). Also $f^{|\alpha|!}$ is an idempotent retraction onto the periodic points.

## Proof sketch

Pointwise, $f^a(x) = f^b(x)$ iff $a \ge \mu(x)$ and $\lambda(x) \mid b - a$; requiring this for all $x$ gives $a \ge \mu_f$ and $\lambda_f \mid b - a$. Hence $f^0, \dots, f^{\mu_f + \lambda_f - 1}$ are distinct and every later power repeats one of them.

## Depends on

- [Functional graphs: transient depth, cycles and canonical cycle representatives](functional-graph-transient-depth-and-cycles.md)

## Sources

- D. E. Knuth, "The Art of Computer Programming, Volume 2: Seminumerical Algorithms", Addison-Wesley, 1997.
