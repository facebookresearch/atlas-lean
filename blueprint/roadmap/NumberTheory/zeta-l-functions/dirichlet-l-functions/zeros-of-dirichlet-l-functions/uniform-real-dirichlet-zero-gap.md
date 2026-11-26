# A uniform logarithmic gap for real Dirichlet zeros

There is a single real $c>0$ such that for every integer modulus $q\ge3$, every primitive nonprincipal
Dirichlet character $\chi$ modulo $q$ with $\operatorname{Im}\chi(a)=0$ for every residue class $a$,
and every real $\beta$ with $0<\beta<1$ and $L(\beta,\chi)=0$, one has

$$
c\le(1-\beta)\log q.
$$

The constant is independent of $q$, $\chi$, and $\beta$. No parity restriction or explicit value
of $c$ is imposed. The conclusion is a gap near $1$, not absence of every real zero in $(0,1)$.

## Expansion

Isolate the uniform estimate for the real-character family in terms of the weighted torus-jet form and its determinant positivity. Relate its critical parameter to $(1-\beta)\log q$ for a genuine real zero of the continued primitive $L$-function; handle both parities before extracting one absolute constant.

## Sources

- [SiegelZeros.lean — `exists_absolute_real_zero_gap`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SiegelZeros.lean#L8-L16)
- [SiegelZeros.lean — `dirichletRealZeroBound_proof`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SiegelZeros.lean#L19-L27)
