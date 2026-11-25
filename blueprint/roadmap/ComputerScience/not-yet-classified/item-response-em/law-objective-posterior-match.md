# Item-response mixture: law, joint and responsibilities

Let $\theta$ be valid mixture parameters with $K$ components over $d$ binary items (positive mixture weights $\pi_k$, item probabilities $p_{kj} \in (0, 1)$), let $x \in \{0, 1\}^d$ and let $k$ be a component. Then:
1. the locally independent item-response mass of $x$ under component $k$ is $\prod_j p_{kj}^{x_j} (1 - p_{kj})^{1 - x_j}$;
2. the joint mixture law sums to $1$ over all patterns and components;
3. for any Markov kernel $\kappa$ from components to patterns and finite measure $\mu$ on components with $\mu\{k'\} = \pi_{k'}$ and $\kappa_{k'}\{x\}$ equal to the item-response mass of $x$ under $k'$ for every $k'$, the responsibility of $k$ for $x$ equals the posterior mass of $\{k\}$ given $x$.
