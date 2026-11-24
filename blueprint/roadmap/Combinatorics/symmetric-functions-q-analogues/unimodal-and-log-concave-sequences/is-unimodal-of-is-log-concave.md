# Log-concave implies unimodal

A log-concave sequence $(a_0, \dots, a_n)$ of nonnegative real numbers with no internal zeros is
unimodal. (In a unimodal sequence any index of a largest term can serve as the peak.)

The hypothesis of no internal zeros cannot be dropped: $1, 0, 0, 1$ is nonnegative and log-concave
but not unimodal. The proof shows that once the sequence
strictly drops at some $i$, log-concavity forces it to keep weakly decreasing, so no later term can
exceed $a_i$; symmetrically for a strict rise.

## Sources

- Richard P. Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011, https://math.mit.edu/~rstan/ec/ec1.pdf, Chapter 1, Exercise 50(a).
