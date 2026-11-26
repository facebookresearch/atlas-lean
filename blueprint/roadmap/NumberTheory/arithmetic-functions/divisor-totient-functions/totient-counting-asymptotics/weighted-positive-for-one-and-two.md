# Positive weighted coefficients at k equal to one and two

For each $k\in\{1,2\}$ there exists a real $c>0$ such that $c\le A(f_k;s)$ for every real
$s\in[0,1)$. The bound may depend on $k$ but not on $s$.

## Depends on

- [Weighted counts and weight](weighted-totient-counts.md)
- [Arithmetic approximants](finite-coefficients.md)

## Proof depends on

- [Positive lower bound from a seed](weighted-positive-seed.md)

## Expansion

Verify the two inequalities $d<\ell(d)$ and $2d<\ell(d)$ for the shared source seed $d=2^{18}\cdot257=67{,}371{,}008$. The totient of $2^{11}\cdot257^2$ is $d$; to prove it is the least preimage, use $p-1\mid d$ for every prime divisor $p$ of a preimage, verify the resulting finite list of possible primes, and apply the prime-power totient constraints to rule out smaller preimages. This gives $\ell(d)=135{,}268{,}352$, with $2d=134{,}742{,}016<\ell(d)$. Apply the conditional positive-seed lower bound to each $k$; convergence of the normalized counts alone cannot prove that this bound is positive.

## Sources

- [TotientAsymptotic.lean — `weighted_totient_one_two`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TotientAsymptotic.lean#L141-L146)
- [Both seed inequalities with the common certified value](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/NumberTheory/TotientAsymptotic/Arithmetic.lean#L177-L184)
- [Finite prime choices and a totient witness](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/NumberTheory/TotientAsymptotic/SeedArithmetic.lean#L12-L36)
- [Minimality of the source seed’s preimage](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/NumberTheory/TotientAsymptotic/SeedMinimum.lean#L65-L106)
- [Unconditional seed application](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/NumberTheory/TotientAsymptotic/SeedConsequences.lean#L10-L24)
