# Finite sums of independent Poisson variables are Poisson

Let $(K_i)_{i \in I}$ be mutually independent $\mathbb{N}$-valued random variables on a probability
space with $K_i \sim \operatorname{Poisson}(\lambda_i)$, $\lambda_i \ge 0$, for every $i \in I$. Then
for every finite set $s \subseteq I$,

$$\sum_{i \in s} K_i \sim \operatorname{Poisson}\Bigl(\sum_{i \in s} \lambda_i\Bigr),$$

where for $s = \emptyset$ both sides are the point mass at $0$. This follows from the two-variable
case by induction on $s$.

## Sources

- T. L. Griffiths and Z. Ghahramani, *The Indian buffet process: an introduction and review*,
  Journal of Machine Learning Research 12 (2011), 1185–1224, Section 4.6.
