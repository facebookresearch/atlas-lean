# Arrow's impossibility theorem for weak preferences

Let $A$ be a type of alternatives
containing three distinct elements, and let $E$ be a finite nonempty set of voters. A profile
$P$ assigns to every voter $v$ a relation $P_v$ on $A$; it is admissible if, for every $v \in E$,
$P_v$ is a total preorder (reflexive, transitive, and $P_v(x, y)$ or $P_v(y, x)$ for all
$x, y \in A$). For a relation $R$ on $A$, say $R$ strictly ranks $a$ above $b$ if $R(a, b)$ holds
and $R(b, a)$ does not. Then there is no map $F$, sending each profile $P$ to a relation $F(P)$
on $A$, with all of the following properties. (Unrestricted domain) $F(P)$ is a total preorder
for every admissible $P$. (Pareto) For every admissible $P$ and all $a, b \in A$, if $P_v$
strictly ranks $a$ above $b$ for every $v \in E$, then $F(P)$ strictly ranks $a$ above $b$.
(Independence of irrelevant alternatives) For all admissible $P, Q$ and $a, b \in A$, if
$P_v(a, b) \iff Q_v(a, b)$ and $P_v(b, a) \iff Q_v(b, a)$ for every $v \in E$, then
$F(P)(a, b) \iff F(Q)(a, b)$ and $F(P)(b, a) \iff F(Q)(b, a)$. (Non-dictatorship) For every
$d \in E$ there are an admissible $P$ and $a, b \in A$ such that $P_d$ strictly ranks $a$ above
$b$ but $F(P)$ does not.

## Sources

- https://en.wikipedia.org/wiki/Arrow%27s_impossibility_theorem.
