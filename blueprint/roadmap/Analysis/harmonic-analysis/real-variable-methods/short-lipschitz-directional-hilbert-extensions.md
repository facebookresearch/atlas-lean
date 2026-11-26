# Fixed-scale Hilbert transforms along unit Lipschitz directions

There exist $a\in(0,1/2)$ and a real $C>0$ such that for every $1$-Lipschitz unit field $v:\mathbb R^2\to\mathbb R^2$ the following hold. For each complex Schwartz $f$ and $0<\epsilon<a$, the two-sided integral $T_\epsilon f(x)=\int_{-a}^{-\epsilon} f(x-tv(x))\,dt/t+\int_\epsilon^a f(x-tv(x))\,dt/t$ has $L^2$ norm at most $C\|f\|_2$. Put $g_x(t)=f(x-tv(x))-f(x+tv(x))$ and $P f(x)=\int_0^a g_x(t)\,dt/t$, with the quotient at $0$ defined by $g_x'(0)$. Then $\|P f\|_2\leq C\|f\|_2$ and, for each finite real $\lambda>0$, the set $\{|P f|>\lambda\}$ has area at most $\lambda^{-2}(C\|f\|_2)^2$. Each $T_\epsilon$ and $P$ has a complex-linear continuous extension $L^2\to L^2$ of norm at most $C$, agreeing almost everywhere with the specified formula on Schwartz inputs.

## Depends on

The actual two-sided hard cutoff and the symmetrized derivative-extended quotient, the Euclidean metric for the Lipschitz hypothesis, and complex $L^2$ modulo null sets.

## Proof depends on

Short-time directional $L^2$ control, passage to the principal value on smooth data, and density of Schwartz functions in $L^2$.

## Expansion

Separate uniform cutoff bounds from the limit and weak-type distribution bound; then exhibit the two kinds of bounded extensions with the specified a.e. agreements. The same $a,C$ must serve the entire field class and every asserted estimate.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/LipschitzHilbert.lean#L61-L66) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/083.md).
