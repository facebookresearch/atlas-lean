# Totients with least preimages in a moving band

For a natural $k\ge1$ and real $x$, let $N_k(x)$ be the number of distinct positive totient values
$v\le\lfloor x\rfloor_+$ with $kx<\ell(v)\le(k+1)x$. The lower endpoint is strict and the upper
endpoint is weak. Define

$$
f_k(r)=\min(1,(k+1)/r)-\min(1,k/r).
$$

Division is totalized; in every arithmetic coefficient the weight is evaluated at the positive
least-preimage ratio $r=\ell(v)/v$.

## Depends on

- [Totient values and arithmetic approximants](finite-coefficients.md)

## Expansion

Build the counts using the minimum positive preimage, not a multiplicity count. Relate the finite count in the open–closed band to the difference of the two truncated ratios when proving the weighted estimates.

## Sources

- [TotientAsymptotic.lean — `weighted_totient_asymptotic`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TotientAsymptotic.lean#L128-L140)
- [TotientAsymptotic.lean — `weighted_totient_one_two`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TotientAsymptotic.lean#L141-L146)
- [TotientCompanionZero.lean — `companion_zero_case`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TotientCompanionZero.lean#L93-L100)
- [Source band count, weight and normalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TotientAsymptotic.lean#L104-L116)
