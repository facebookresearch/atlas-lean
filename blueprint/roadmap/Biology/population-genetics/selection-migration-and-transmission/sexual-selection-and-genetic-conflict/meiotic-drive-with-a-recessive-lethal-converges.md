# A recessive lethal limits meiotic drive except at complete transmission

Consider a deterministic infinite diploid population with random mating,
nonoverlapping generations and equal gamete frequencies in both sexes.
A heterozygote transmits $D$ with probability $k\in[1/2,1]$ in either
sex. Zygote viabilities are $w_{DD}=0$ and $w_{Dd}=w_{dd}=1$;
surviving genotypes contribute equal numbers of gametes. No mutation,
drift or additional fertility effect is included.
If the current gamete frequency is $p\in[0,1)$, random union gives
zygote frequencies $p^2,2p(1-p),(1-p)^2$ and positive mean viability
$\overline w=1-p^2$. The next gamete frequency is

$$F_k(p)=\frac{2kp(1-p)}{1-p^2}=\frac{2kp}{1+p}.$$

For $1/2<k<1$, there is a unique interior fixed point
$p_*=2k-1$. Every $0<p_0<1$ converges monotonically to $p_*$,
with no overshoot; starting at $p_*$ is constant. Its local derivative
is $F_k'(p_*)=1/(2k)<1$.
For $k=1/2$, $p_t=p_0/(1+tp_0)$ and the allele tends to zero.
For $k=1$, every $0<p_0<1$ increases toward the boundary $1$;
there is **no interior equilibrium**, and $\overline w_t=1-p_t^2\to0$.
For all $k$, $p_0=0$ stays zero.

The biological recurrence is undefined at $p=1$: every zygote is $DD$
and no adult survives. Cancellation in the rational formula must not be
used to give that extinct population a next gamete pool. For $k=1$ the
boundary is approached only as a limit of productive finite generations;
this is not an interior polymorphic balance or a demographic persistence
result.

## Background

- [Canonical meiotic drive without viability differences](../one-locus-selection-dynamics/meiotic-drive-without-viability-differences.md)

## Expansion

For $a=2k-1$, direct subtraction gives
$F_k(p)-p=p(a-p)/(1+p)$ and $F_k(p)-a=(p-a)/(1+p)$.
These establish direction and absence of overshoot. Continuity identifies
the monotone limit. For $p_0>0$, reciprocal frequencies satisfy
$p_{t+1}^{-1}=(p_t^{-1}+1)/(2k)$; at $k=1/2$ this yields the stated
exact trajectory. At $k>1/2$ it yields
$p_t^{-1}=(2k)^{-t}p_0^{-1}+[1-(2k)^{-t}]/(2k-1)$,
also proving the endpoint $k=1$ limit.
This is a separate viability-cost model, not a restatement of the
canonical cost-free transmission theorem.

## Sources

- The specified random-mating, viability and transmission model is derived above; no broader biological invasion or population-survival theorem is asserted.
