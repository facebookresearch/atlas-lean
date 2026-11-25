# Symmetrization lemma

Let $\mu$ be a probability measure on $Z$ and $f_1, \dots, f_M$ measurable functions with $f_j \in [0, 1]$ $\mu$-a.e. Let $\varepsilon > 0$ and $n \varepsilon^2 \ge 2$. For samples $S, S'$ of $n$ independent draws from $\mu$, let

$$D(S) = \max_j \Bigl|\tfrac1n \sum_i f_j(S_i) - \textstyle\int f_j\,d\mu\Bigr|, \qquad D'(S, S') = \max_j \Bigl|\tfrac1n \sum_i f_j(S_i) - \tfrac1n \sum_i f_j(S'_i)\Bigr|.$$

Then $P(D(S) > \varepsilon) \le 2\,P(D'(S, S') > \varepsilon/2)$.

This is Lemma 12.1 of L. Devroye, L. Györfi and G. Lugosi, *A Probabilistic Theory of Pattern Recognition*, Springer (1996).
