# Entropy of a product distribution on words

Let $S$ be a finite set and $a : S \to \mathbb{R}$ with $\sum_{s \in S} a(s) = 1$, for instance a probability
vector. Write $\eta(t) = -t \log |t|$ for $t \ne 0$ and $\eta(0) = 0$. Then for every $n \ge 0$,

$$\sum_{w \in S^n} \eta\bigl(a(w_0)\, a(w_1) \cdots a(w_{n-1})\bigr) = n \sum_{s \in S} \eta(a(s)).$$

For a probability vector $a$ this says that the entropy of $n$ independent letters with law $a$ is $n$ times the
entropy of one.
