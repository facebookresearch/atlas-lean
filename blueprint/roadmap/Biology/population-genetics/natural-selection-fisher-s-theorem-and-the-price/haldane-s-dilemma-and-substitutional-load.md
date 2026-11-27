# Logarithmic substitution cost and a reproductive budget in haploid selection

In the deterministic two-type [selection model](select.md), the fitnesses
are $1$ and $1-s$, with $0<s<1$. Start the fitter type at $0<p_0<1$, and set
$p_{t+1}=p_t/\bar w_t$, where $\bar w_t=1-s(1-p_t)$. Define logarithmic cost
and ordinary load by

$$D=\sum_{t=0}^\infty-\log\bar w_t,\qquad L_t=1-\bar w_t.$$

Then the nonnegative series converge and satisfy

$$D=\log(1/p_0),\qquad
 (1-s)\log(1/p_0)\le\sum_{t=0}^\infty L_t\le\log(1/p_0).$$

In particular weak selection gives a uniform relative-error bound of at
most $s$ when approximating the ordinary cumulative load by $D$. Weak
selection is sufficient, not necessary, for a close approximation.

A reproductive-budget interpretation requires an additional model. Suppose
a deterministic positive abundance $Z_t$ satisfies
$Z_{t+1}=R_t\bar w_t Z_t$ for specified baseline reproductive multipliers
$R_t>0$ that are the same for both types. Put
$B_T=\sum_{t=0}^{T-1}\log R_t$. For every integer $T\ge0$,

$$\log(Z_T/Z_0)=B_T-\log(p_T/p_0).$$

Consequently $Z_T\ge Z_0$ exactly when $B_T\ge\log(p_T/p_0)$.
Maintaining $Z_t\ge Z_0$ at every horizon requires this inequality at every
horizon, not only at a single final time. These are claims about the stated
deterministic abundance model, not a stochastic extinction probability or
a universal evolutionary speed limit.

## Depends on

- [Selection map](select.md)

## Proof depends on

- [Closed form for repeated haploid selection](../haploid-selection-and-multiplicative-fitnesses/iterate-select.md)

## Expansion

The closed form gives $p_t=p_0/[p_0+(1-p_0)(1-s)^t]\to1$.
For each finite $T$, $\sum_{t<T}-\log\bar w_t=\log(p_T/p_0)$ by telescoping;
take the limit. For $0\le L_t\le s<1$,
$L_t\le-\log(1-L_t)\le L_t/(1-s)$, which proves both bounds and summability.
Multiplying the abundance recursion proves the budget identity. The
logarithmic cost defined here is not silently identified with a historical
selective-death approximation.

## Sources

- J. B. S. Haldane, "The cost of natural selection", Journal of Genetics 55 (1957), 511–524, <https://doi.org/10.1007/BF02984069>, bibliographic background only. The precise identities and bounds above are derived here; they are not claimed as a transcription of that paper.
