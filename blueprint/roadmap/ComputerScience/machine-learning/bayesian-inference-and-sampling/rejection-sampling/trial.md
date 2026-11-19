# One round of rejection sampling

Let $p$ and $q$ be probability mass functions on a type
$\alpha$ (the target and the proposal) and let $M \in [0, \infty]$ be an envelope constant with
$p(x) \le M\,q(x)$ for all $x \in \alpha$. One round of rejection sampling for target $p$, proposal
$q$ and envelope $M$ is the probability mass function on pairs
$(x, b) \in \alpha \times \{\mathrm{true}, \mathrm{false}\}$ obtained by drawing $x$ from $q$ and
then flipping a coin that lands $b = \mathrm{true}$ ("accepted") with probability
$p(x) / (M\,q(x))$.
