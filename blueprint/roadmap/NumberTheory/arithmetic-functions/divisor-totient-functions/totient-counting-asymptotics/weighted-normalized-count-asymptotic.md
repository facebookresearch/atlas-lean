# Normalized weighted totient counts

Fix a natural $k\ge1$. Without any seed assumption,

$$
N_k(x)/U(x)-A(f_k;\theta(x))\longrightarrow0\qquad (x\to+\infty,\ x\in\mathbb R).
$$

## Depends on

- [Weighted counts](weighted-totient-counts.md)
- [Renewal normalization](totient-counting-normalization.md)
- [Arithmetic approximants](finite-coefficients.md)

## Proof depends on

- [Uniform convergence of the weighted coefficient](weighted-coefficient-uniform-convergence.md)

## Expansion

Establish fixed-band asymptotics with the least-preimage weight and a uniform error for its approximation by tail data. Pass to the uniform coefficient limit without dividing by a possibly zero coefficient.

## Sources

- [TotientAsymptotic.lean — `weighted_totient_asymptotic`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TotientAsymptotic.lean#L128-L140)
