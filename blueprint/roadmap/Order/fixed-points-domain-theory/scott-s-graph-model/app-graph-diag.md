# Scott's first recursion theorem in `P(ω)`

For $u \subseteq \mathbb{N}$, let $d = \operatorname{graph}(x \mapsto \operatorname{app}(u, \operatorname{app}(x, x)))$, the denotation of $\lambda x.\, u(x\,x)$. Then the self-application of $d$ is the least fixed point of the continuous function $\operatorname{app}(u, \cdot)$:

$$\operatorname{app}(d, d) = \bigcup_{k \ge 0} \operatorname{app}(u, \cdot)^k(\emptyset).$$

Since the paradoxical combinator $Y = \lambda u.(\lambda x.u(xx))(\lambda x.u(xx))$ sends $u$ to $\operatorname{app}(d, d)$, this says that $Y$ computes least fixed points (D. Scott, *Data types as lattices*, SIAM J. Comput. 5(3) (1976), 522–587, Theorem 2.5, stated there for $u$ the graph of a continuous $f$; every $u$ determines the continuous function $\operatorname{app}(u, \cdot)$).

Scott's proof shows by β-conversion that $\operatorname{app}(d, d)$ is a fixed point, and then by induction on the index $l$ of finite sets $e_l \subseteq d$ that $\operatorname{app}(e_l, e_l)$ lies below every fixed point. The induction uses that $k \in e_l$ implies $k < l$ and that $n \le \langle n, m\rangle$.

## Informally uses

- [Scott's graph theorem, part (i)](app-graph.md): the β-calculation showing that $\operatorname{app}(d, d)$ is a fixed point.
- [Elements of the `n`-th finite set are smaller than `n`](lt-of-mem-fin-set.md): the property of the enumeration that drives the induction.

## Background

- [Kleene's fixed-point theorem for pointed dcpos](../scott-continuous-maps-and-least-fixed-points/map-i-sup-iterate-bot.md): the least fixed point as the union of the iterates. Scott remarks that his proof does not use the fixed-point theorem itself.
- [Scott's first recursion theorem](../../../ComputerScience/programming-language-semantics/models-of-the-untyped-lambda-calculus/app-denote-y.md): the same theorem for the λ-term $Y$.

## Sources

- D. Scott, *Data types as lattices*, SIAM Journal on Computing 5(3) (1976), 522–587, doi:10.1137/0205037.
