# Likelihood of a response pattern

Let $Z$ be a finite set of latent states and $\iota$ a finite set of items, with fixed item success probabilities $P_z(i) \in (0, 1)$ for each latent state $z$ and item $i$. The item likelihood of a response pattern $x \in \{0, 1\}^\iota$ at latent state $z$ is the locally independent response probability $P_z(x) = \prod_i P_z(i)^{x_i} (1 - P_z(i))^{1 - x_i}$.
