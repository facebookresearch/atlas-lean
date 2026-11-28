# The weights-only EM step

Let $Z$ be a finite set of latent states and $\iota$ a finite set of items, with fixed item success probabilities $P_z(i) \in (0, 1)$ for each latent state $z$ and item $i$. Let $Z$ be nonempty and $x_1, \dots, x_N$ response patterns with $N \ge 1$. The weights-only EM step keeps the item parameters fixed and maps valid weights $w$ to the posterior-average weights $w'_z = \frac{1}{N} \sum_n p_w(z \mid x_n)$.
