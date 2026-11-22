# Myerson's Lemma 2 for one bidder

A single-parameter mechanism is given by an allocation rule $Q : \mathbb{R} \to \mathbb{R}$ and a payment rule $P : \mathbb{R} \to \mathbb{R}$: an agent of value $t$ who reports $s$ gets the utility $t\,Q(s) - P(s)$, and $U(t) = t\,Q(t) - P(t)$ is its truthful utility.
Let $a \le b$ and $Q \ge 0$ on $[a, b]$. The mechanism $(Q, P)$ is incentive compatible on $[a, b]$ and
individually rational ($U(t) \ge 0$ for all $t \in [a, b]$) if and only if $Q$ is monotone on $[a, b]$, the
envelope formula $U(t) = U(a) + \int_a^t Q(x)\,dx$ holds for every $t \in [a, b]$, and $U(a) \ge 0$
(Myerson 1981, Lemma 2, (4.2)–(4.4), for a single bidder without revision effects). Of Myerson's probability
conditions (3.3), which for one bidder read $0 \le Q \le 1$, only the nonnegativity $Q \ge 0$ is used; the
upper bound $Q \le 1$ is not needed.

## Informally uses

- [Myerson's lemma](is-incentive-compatible-on-iff.md): the incentive constraints.
- [Individual rationality from the lowest type](utility-nonneg-of-lowest.md): the participation constraints.

## Sources

- R. B. Myerson, "Optimal auction design", *Mathematics of Operations Research* 6(1) (1981), 58–73, Lemma 2.
