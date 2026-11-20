# Security by reduction

Suppose a reduction maps every admissible adversary family $A$ against a scheme to an admissible
family $B$ against an assumption, with
$$\mathrm{adv}_n(A_n) \le \mathrm{adv}'_n(B_n) + \delta(n)$$
for every $n$, where $\delta$ is a negligible advantage. If the assumption is asymptotically secure,
then so is the scheme. This is the shape of a security proof by a reduction that loses only an
additive negligible term.
