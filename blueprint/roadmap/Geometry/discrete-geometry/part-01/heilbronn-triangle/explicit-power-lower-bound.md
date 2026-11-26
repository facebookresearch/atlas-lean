# An explicit power lower bound for Heilbronn triangles along a sequence

For $p,q,r\in[0,1]^2$ let $A(p,q,r)=\frac12|\det(q-p,r-p)|$. Put $M=\binom{163}{41}$, $T=\binom M3$, and $\eta=1/(100000(T^2+1))$.

The number $\eta$ is positive. There are sequences $n_j\to\infty$ and $P_j\subseteq[0,1]^2$ of finite sets with $|P_j|=n_j\ge3$ such that $A(p,q,r)\ge n_j^{-2+\eta}$ for every triple of pairwise distinct points of $P_j$. The selected assertion gives sizes tending to infinity, not every sufficiently large size.

## Depends on

- Determinant area, exact combinatorial exponent and finite subsets of the closed unit square.

## Proof depends on

- Construct the sequence with the stated determinant separation and prove that its sizes diverge.

## Expansion

Separate the finite configuration construction from the asymptotic divergence. Preserve the explicit exponent instead of replacing it by an existential positive exponent.

## Sources

- OpenAI Math, [`heilbronn_power_lower_bound`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HeilbronnTriangle.lean#L51-L58) (statement and local definitions).
