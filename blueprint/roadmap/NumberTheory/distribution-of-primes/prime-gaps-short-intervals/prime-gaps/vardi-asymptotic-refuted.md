# Vardi's prime-gap asymptotic is false

Let $\pi$ be the prime-counting function and, for
real $x$, let $d(x)$ be the largest prime gap $p_{n+1} - p_n$ over the primes $p_n < x$. It is
not true that for every real $C > 1$,
$\pi(\lfloor y + C\,d(x) \rfloor) - \pi(\lfloor y \rfloor)$ is asymptotically equivalent to
$C\,d(x) / \log y$ as $x \to \infty$ over pairs $(x, y)$ with $x/2 < y < x$.

This resolves Erdős Problem 1138 in the negative (Sunder, Kumrawat and Cheri, with GPT 5.5;
the disproof is Lean-verified).

## Sources

- Sunder, Kumrawat, Cheri, and GPT 5.5 (Lean-verified disproof), per erdosproblems.com/1138, https://www.erdosproblems.com/1138; Hrishi Sunder, Sourish Kumrawat, and Kireet Cheri, An Elementary Obstruction to a Uniform Prime-Gap Asymptotic (2026), https://github.com/sourish-kumrawat/sourish-kumrawat.github.io/blob/adcbf7ea4e6f57b84001c372a7f8093c95fe7b10/papers/Erdos_1138.pdf; Lean disproof of Erdos Problem 1138, YanYablonovskiy/formal-conjectures, https://github.com/YanYablonovskiy/formal-conjectures/blob/7c134317104d3b98ecc751afbb79ec0adddf8e7c/FormalConjectures/ErdosProblems/1138a.lean#L497.
