# Uniqueness for the first-step equation of rejection sampling

Let $p$ and $q$ be
probability mass functions on $\alpha$ and $M \in [0, \infty]$ with $M \ne 0$, $M \ne \infty$ and
$p(y) \le M\,q(y)$ for all $y \in \alpha$. For one round of rejection sampling for target $p$,
proposal $q$ and envelope $M$, write $P(x, \mathrm{accepted})$ for the probability that the round
proposes $x$ and accepts it, and $r$ for the sum over $y \in \alpha$ of the probabilities that it
proposes $y$ and rejects it. If $f \colon \alpha \to [0, \infty]$ takes only finite values and
satisfies $f(x) = P(x, \mathrm{accepted}) + r \, f(x)$ for every $x \in \alpha$, then $f(x) = p(x)$
for every $x \in \alpha$.

The law of the output of the loop that repeats independent rounds until one accepts satisfies this
first-step equation, so this result identifies that law as $p$.
