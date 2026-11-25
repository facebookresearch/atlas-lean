# Posterior inclusion probability

Let $w$ be [prior weights](prior-weights.md) on a finite set $\iota$ and let $\mathrm{BF} : \iota \to \mathbb{R}$ be arbitrary. The posterior inclusion probability of $j \in \iota$ is

$$\mathrm{PIP}_j(w, \mathrm{BF}) = \frac{w_j \,\mathrm{BF}_j}{\sum_{k \in \iota} w_k \,\mathrm{BF}_k},$$

the [normalized weighted evidence](normalized-weighted-evidence.md), with the convention $x / 0 = 0$. When every $\mathrm{BF}_k$ is positive the denominator is positive and these values form a probability distribution on $\iota$.
