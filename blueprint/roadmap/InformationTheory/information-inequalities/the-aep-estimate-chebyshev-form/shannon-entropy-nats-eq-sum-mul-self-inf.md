# Shannon Entropy Nats eq sum mul self Information

Let $\alpha$ be a finite set and $p$ a probability mass function on $\alpha$. Let $I_p(a) = -\log p(a)$ when $p(a) > 0$ and $I_p(a) = 0$ when $p(a) = 0$. Then the entropy in nats is the expectation of $I_p$:

$$-\sum_{a \in \alpha} p(a) \log p(a) = \sum_{a \in \alpha} p(a)\, I_p(a),$$

with $0 \log 0 = 0$; the values of $I_p$ at outcomes of probability zero do not affect the sum.
