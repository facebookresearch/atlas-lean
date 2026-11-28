# Joint likelihood of a list of observations

For a finite set $\Theta$ and a list $L_1, \dots, L_k$ of likelihood weights $L_j : \Theta \to \mathbb{R}$, the batch likelihood is the pointwise product $\theta \mapsto \prod_{j=1}^k L_j(\theta)$, equal to $1$ for the empty list.
