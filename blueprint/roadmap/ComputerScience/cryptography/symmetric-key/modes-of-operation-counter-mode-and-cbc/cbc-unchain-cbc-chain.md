# CBC unchaining inverts chaining

Let $X$ be an additive commutative group and let $p, p' \colon X \to X$ with $p'$ a left inverse of $p$: $p'(p(x)) = x$ for every $x$. For every length $n$, initial value $\mathrm{iv}$ and message $m \in X^n$, [unchaining](cbc-unchain.md) the CBC chain of $m$ with $p'$ from $\mathrm{iv}$ recovers $m$. Only a left inverse is needed, but commutativity is used: $(\mathrm{iv} + m) - \mathrm{iv} = m$ can fail in a noncommutative group.
