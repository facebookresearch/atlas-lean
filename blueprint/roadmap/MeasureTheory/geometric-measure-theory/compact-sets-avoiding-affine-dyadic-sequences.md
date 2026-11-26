# Compact sets avoiding every affine dyadic sequence

For each real $0<\eta<1$ there is a compact set $E\subseteq[0,1]$ of Lebesgue measure strictly greater than $1-\eta$ such that for every $x\in\mathbb R$ and every $s\in\mathbb R\setminus\{0\}$ there is an integer $n\geq1$ with $x+s2^{-n}\notin E$. The same $E$ must work for both signs of $s$ and all translations. The ratio is exactly $1/2$.

## Depends on

- [Lebesgue measure on the real line](../lebesgue-measure/lebesgue-measure-on-euclidean-spaces/lebesgue-measure-on-the-real-line/lebesgue-measure.md), for the length convention on $[0,1]$.

## Proof depends on

The construction needs arbitrarily small open $1$-periodic hitting sets for the normalized positive scales: for each $0<p<1$, an open set $H$ with $H+1=H$ and $|H\cap[0,1)|\leq 6p$ that meets $\{x+t2^{-n}:n\geq1\}$ for every $x\in\mathbb R$ and $t\in[1,2]$.

## Expansion

Separate the normalized hitting-set lemma from the lift to all nonzero scales. Break the hitting-set construction into the finite window and routing construction with a uniform failure bound, followed by an open periodic repair with measure at most $6p$ per period. For the lift, choose a summable budget of normalized sets, take their dyadic pullbacks and reflected pullbacks, and use a tail shift to move each scale into $[1,2]$. The deletion from $[0,1]$ must have length at most $\eta/2$, so its compact complement has the required strict lower bound.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DyadicAvoidance.lean#L12-L19) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/084.md).
- OpenAI, [periodic hitting theorem and its use](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/MeasureTheory/DyadicAvoidance/Main.lean#L81-L105).
