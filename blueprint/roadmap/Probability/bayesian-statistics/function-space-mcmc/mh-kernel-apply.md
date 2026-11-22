# Evaluation of the Metropolis–Hastings kernel

For a Markov kernel $Q$, a measurable potential $\Phi$, a point $u$ and a measurable set $B$, the [Metropolis–Hastings kernel](mh-kernel.md) satisfies

$$
P(u, B) = \int_B a(u, v) \, Q(u, dv) + \mathbf 1_B(u) \int (1 - a(u, w)) \, Q(u, dw),
$$

the probability of an accepted move into $B$ plus the probability of rejection when $u \in B$.

## Sources

- Masoumeh Dashti and Andrew M. Stuart, *The Bayesian approach to inverse problems*, in *Handbook of Uncertainty Quantification*, Springer (2017), 311–428, DOI 10.1007/978-3-319-12385-1_7; numbering of arXiv:1302.6989v4 (2015), equation (5.5).
