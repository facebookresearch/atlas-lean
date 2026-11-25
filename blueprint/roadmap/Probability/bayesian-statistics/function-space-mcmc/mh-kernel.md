# Metropolis–Hastings kernel for a prior-reversible proposal

Let $Q$ be a Markov kernel on a measurable space $U$ (the proposal) and $\Phi : U \to \mathbb{R}$ a measurable potential. From $u$, propose $v \sim Q(u, \cdot)$ and accept it with probability $a(u, v) = \min\{1, e^{\Phi(u) - \Phi(v)}\}$;
otherwise stay at $u$. As a Markov kernel,

$$
P(u, dv) = a(u, v) \, Q(u, dv) + \Big( \int (1 - a(u, w)) \, Q(u, dw) \Big) \, \delta_u(dv) .
$$

## Sources

- Masoumeh Dashti and Andrew M. Stuart, *The Bayesian approach to inverse problems*, in *Handbook of Uncertainty Quantification*, Springer (2017), 311–428, DOI 10.1007/978-3-319-12385-1_7; numbering of arXiv:1302.6989v4 (2015), Algorithm 5.6 and equation (5.5).
