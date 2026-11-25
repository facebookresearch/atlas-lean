# Envelope formula

A single-parameter mechanism is given by an allocation rule $Q : \mathbb{R} \to \mathbb{R}$ and a payment rule $P : \mathbb{R} \to \mathbb{R}$: an agent of value $t$ who reports $s$ gets the utility $t\,Q(s) - P(s)$, and $U(t) = t\,Q(t) - P(t)$ is its truthful utility.
If $(Q, P)$ is incentive compatible on $[a, b]$, then for every $t \in [a, b]$

$$U(t) = U(a) + \int_a^t Q(x)\,dx$$

(Myerson 1981, (4.3)).

## Informally uses

- [Myerson's inequality (4.6)](is-incentive-compatible-on-iff-utility.md): it squeezes the increments of the utility between $(t - s)\,Q(s)$ and $(t - s)\,Q(t)$.
- [Two-sided comparison lemma](eq-of-abs-sub-le-mul.md): the Riemann-sum argument that turns these bounds into the integral.

## Sources

- R. B. Myerson, "Optimal auction design", *Mathematics of Operations Research* 6(1) (1981), 58–73, proof of Lemma 2, (4.3).
