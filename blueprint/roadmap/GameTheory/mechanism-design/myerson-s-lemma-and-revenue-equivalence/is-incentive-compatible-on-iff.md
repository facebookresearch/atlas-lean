# Myerson's lemma

A single-parameter mechanism is given by an allocation rule $Q : \mathbb{R} \to \mathbb{R}$ and a payment rule $P : \mathbb{R} \to \mathbb{R}$: an agent of value $t$ who reports $s$ gets the utility $t\,Q(s) - P(s)$, and $U(t) = t\,Q(t) - P(t)$ is its truthful utility.
For all reals $a, b$, the mechanism $(Q, P)$ is incentive compatible on $[a, b]$ if and only if $Q$ is
monotone (nondecreasing) on $[a, b]$ and $U(t) = U(a) + \int_a^t Q(x)\,dx$ for every $t \in [a, b]$
(Myerson 1981, Lemma 2, conditions (4.2) and (4.3); Nisan 2007, Theorem 9.39; Hartline and Karlin 2007,
Theorem 13.6). No regularity of $Q$ beyond monotonicity is needed.

## Informally uses

- [Monotonicity of incentive-compatible allocations](allocation-monotone-on.md): the first condition.
- [Envelope formula](envelope-formula.md): the second condition.
- [Myerson's inequality (4.6)](is-incentive-compatible-on-iff-utility.md): the converse, from the bounds $(t - s)\,Q(s) \le \int_s^t Q$ for monotone $Q$.

## Sources

- R. B. Myerson, "Optimal auction design", *Mathematics of Operations Research* 6(1) (1981), 58–73, Lemma 2.
- N. Nisan, "Introduction to mechanism design (for computer scientists)", Chapter 9 of N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, Theorem 9.39 (whose proof assumes differentiability almost everywhere).
- J. D. Hartline and A. R. Karlin, "Profit maximization in mechanism design", Chapter 13 of the same volume, Theorem 13.6.
