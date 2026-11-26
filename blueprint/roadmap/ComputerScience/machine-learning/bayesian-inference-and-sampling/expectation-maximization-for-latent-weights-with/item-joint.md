# Joint probability of a response pattern and a latent state

Let $Z$ be a finite set of latent states and $\iota$ a finite set of items, with fixed item success probabilities $P_z(i) \in (0, 1)$ for each latent state $z$ and item $i$. For valid latent weights $w$, the joint probability of a response pattern $x \in \{0, 1\}^\iota$ and latent state $z$ is $w_z \cdot P_z(x)$, where $P_z(x) = \prod_i P_z(i)^{x_i} (1 - P_z(i))^{1 - x_i}$ is the locally independent response law of $z$.
