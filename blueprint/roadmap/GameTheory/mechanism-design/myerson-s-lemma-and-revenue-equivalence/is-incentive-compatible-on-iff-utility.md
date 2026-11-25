# Myerson's inequality (4.6)

A single-parameter mechanism is given by an allocation rule $Q : \mathbb{R} \to \mathbb{R}$ and a payment rule $P : \mathbb{R} \to \mathbb{R}$: an agent of value $t$ who reports $s$ gets the utility $t\,Q(s) - P(s)$, and $U(t) = t\,Q(t) - P(t)$ is its truthful utility.
For all reals $a, b$, the mechanism $(Q, P)$ is incentive compatible on $[a, b]$ if and only if
$U(s) + (t - s)\,Q(s) \le U(t)$ for all $s, t \in [a, b]$ (Myerson 1981, (4.6)).

## Background

- [Truthful utility](truthful-utility.md): the utility in which the inequality is written.

## Sources

- R. B. Myerson, "Optimal auction design", *Mathematics of Operations Research* 6(1) (1981), 58–73, proof of Lemma 2, (4.6).
