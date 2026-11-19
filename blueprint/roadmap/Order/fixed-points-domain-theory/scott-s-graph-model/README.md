# Scott's graph model

Scott's graph model takes the powerset $P(\omega)$ of the natural numbers, ordered by inclusion, as one universal domain (D. Scott, *Data types as lattices*, SIAM J. Comput. 5 (1976), §1). Its Scott topology has the sets $\{y \mid n \in y\}$ as a subbasis, and its open sets are the sets "of finite character". A Scott-continuous map $f : P(\omega) \to P(\omega)$ is therefore determined by its values on finite sets (Scott's Theorem 1.1). It is coded by its graph $\{\langle n, m\rangle \mid m \in f(e_n)\}$, where $e_n$ is the finite set given by the binary expansion of $n$, and every set $u$ acts as a function $x \mapsto \{m \mid \exists n,\ e_n \subseteq x,\ \langle n, m\rangle \in u\}$. The graph theorem (Theorem 1.2) says that this application recovers every continuous function from its graph, that $u \subseteq \operatorname{graph}(\operatorname{app} u)$, and which sets are graphs. So the continuous self-maps of $P(\omega)$ form a retract of $P(\omega)$: this is what makes $P(\omega)$ a model of the untyped λ-calculus with β-conversion. The retraction is not onto, so η fails. Through self-application, the paradoxical combinator computes least fixed points (Theorem 2.5). Every second-countable $T_0$ space embeds in $P(\omega)$ (Theorem 1.6), and continuous maps into $P(\omega)$ extend from subspaces (Theorem 1.5), which is why Scott called it universal.

Here $e_n$ is Scott's binary enumeration. The pairing is $\langle n, m\rangle = m^2 + n$ if $n < m$ and $\langle n, m\rangle = n^2 + n + m$ otherwise, rather than Scott's Cantor pairing; the proofs use only that pairing is a bijection with $n \le \langle n, m\rangle$.

## The model

- [The `n`-th finite set of the graph model](fin-set.md)
- [Elements of the `n`-th finite set are smaller than `n`](lt-of-mem-fin-set.md)
- [The compact elements of `P(ω)` are the finite sets](is-compact-element-iff-finite.md)
- [Graph of a function on `P(ω)`](graph.md)
- [Application in the graph model](app.md)

## Continuity

- [Scott's characterisation theorem for `P(ω)`](mem-iff-exists-finset-of-scott-continuou.md)
- [Application in `P(ω)` is Scott-continuous in its argument](scott-continuous-app-right.md)
- [Application in `P(ω)` is Scott-continuous in the function](scott-continuous-app-left.md)
- [Application in `P(ω)` is jointly Scott-continuous](scott-continuous-app.md)
- [Self-application is Scott-continuous](scott-continuous-app-diag.md)
- [The graph of a pointwise union](graph-s-sup.md)

## The graph theorem

- [Scott's graph theorem, part (i)](app-graph.md)
- [Scott's graph theorem, part (ii)](subset-graph-app.md)
- [Scott's graph theorem, part (iii)](graph-app-eq-iff.md)
- [The graph model is not extensional](exists-graph-app-ne.md)

## Recursion

- [Scott's first recursion theorem in `P(ω)`](app-graph-diag.md)

## Topology

- [The sets of naturals containing `n` are Scott-open](is-open-set-of-mem.md)
- [Scott-open sets of `P(ω)` have finite character](exists-finset-mem-of-is-open.md)
- [Continuity into `P(ω)` is tested on the subbasic open sets](continuous-of-is-open-set-of-mem.md)
- [Scott's embedding map](is-embedding-set-of-mem.md)
- [Scott's embedding theorem](exists-is-embedding-with-scott.md)
- [Scott's extension of a map into `P(ω)`](extend-scott.md)
- [Scott's extension is continuous](continuous-extend-scott.md)
- [Scott's extension extends a continuous map](extend-scott-apply.md)
- [Scott's extension theorem](exists-continuous-extend-with-scott.md)

## Related topics

- [Models of the untyped lambda calculus](../../../ComputerScience/programming-language-semantics/models-of-the-untyped-lambda-calculus/README.md): the interpretation of λ-terms in $P(\omega)$, with soundness of β-reduction.
- [Scott-continuous maps and least fixed points](../scott-continuous-maps-and-least-fixed-points/README.md): function spaces and Kleene's fixed-point theorem in general dcpos.
- [Scott's inverse-limit theorem](../scott-s-inverse-limit-theorem.md): the extensional model $D_\infty \cong [D_\infty \to D_\infty]$.
- [Continuous lattices](../continuous-lattices/README.md): the injective spaces, of which $P(\omega)$ is one.
