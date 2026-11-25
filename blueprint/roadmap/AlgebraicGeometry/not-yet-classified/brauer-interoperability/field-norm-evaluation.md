# Field norm evaluation

Projection formula for norms: let $l/k$ be a finite extension of perfect fields, $X$ a smooth
proper $k$-scheme and $Y$ a smooth proper $l$-scheme with a Cartesian square `E` exhibiting
$Y \to X$ as the base change of $X$ to $l$; let $N : \mathrm{CH}_0(Y) \to \mathrm{CH}_0(X)$ be a map
induced by pushforward of zero-cycles, $\sigma$ a $k$-embedding of $l$ into the separable closure of
$k$ with a `FiniteFieldPair` $P$, and $\mathrm{cor} : \mathrm{Br}(l) \to \mathrm{Br}(k)$ a
corestriction given on cocycle classes by the transfer formula. If $b \in \mathrm{Br}(Y)$ is the
pullback of $a \in \mathrm{Br}(X)$, then for every $z \in \mathrm{CH}_0(Y)$ the descended evaluation
`zero_cycle_descent` of $a$ at $N(z)$ is $\mathrm{cor}$ of the descended evaluation of $b$ at
$z$.
