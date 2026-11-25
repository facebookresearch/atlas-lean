# Invasion and loss in a specified maternal-transmission model

Consider a deterministic discrete-generation population.
An infected mother transmits an element to fraction $1-\mu$ of her viable
offspring, with $0\le\mu<1$; an uninfected mother never transmits it.
Let $w_I,w_U>0$ be the reproductive weights of infected and uninfected
females. Assume an infection-independent daughter fraction, no other
infection-dependent survival between the frequency census and reproduction,
and no paternal contribution to these reproduction/transmission rules.
For female infection frequency $c\in[0,1]$ the next frequency is

$$F(c)=\frac{(1-\mu)w_Ic}{w_Ic+w_U(1-c)}.$$

Put $A=(1-\mu)w_I$ and $B=w_I-w_U$.
The map preserves $[0,1]$, and its multiplier at zero is $A/w_U$.
Thus strict invasion from sufficiently small positive frequency occurs
exactly when $A>w_U$; the absent state $c=0$ itself stays absent.
The complete deterministic limits are:

- If $\mu>0$ and $A>w_U$, every $c_0>0$ converges monotonically,
  without overshoot, to the unique interior fixed point
  $c_*=(A-w_U)/(w_I-w_U)$.
- If $\mu>0$ and $A\le w_U$, every $c_0>0$ decreases to zero.
  Equality is a critical, still losing case, not strict invasion.
- If $\mu=0$ and $w_I>w_U$, every $c_0>0$ tends to one.
- If $\mu=0$ and $w_I<w_U$, every $c_0<1$ tends to zero, but
  $c_0=1$ stays one: without transmission failure no uninfected offspring
  can appear in an all-infected population.
- If $\mu=0$ and $w_I=w_U$, every frequency is fixed.

Male phenotypes drop out **under the specified paternal-independent
reproduction rules**, not merely because males fail to transmit the
element. Paternal fertility effects, mating effects or cytoplasmic
incompatibility can change the recurrence and are outside this model.

## Expansion

The denominator is a positive convex combination of $w_I,w_U$.
The map is increasing, with derivative $Aw_U/(w_U+Bc)^2$, and
$F(c)-c=c(A-w_U-Bc)/(w_U+Bc)$. These facts give the fixed points,
direction of motion and absence of overshoot in the invasion case.
When $\mu>0,A\le w_U$, the affine numerator factor is nonpositive at
zero and strictly negative at one (where it is $-\mu w_I$), so it is
strictly negative for $0<c\le1$. At $\mu=0$,
$F(c)-c=Bc(1-c)/(w_U+Bc)$, proving the remaining cases.
For $c_0>0$, the exact reciprocal recursion is
$c_{t+1}^{-1}=(w_U/A)c_t^{-1}+B/A$.
At the critical case $\mu>0,A=w_U$, this gives
$c_t^{-1}=c_0^{-1}+tB/w_U$, showing algebraic rather than geometric
loss. No stochastic finite-population persistence claim follows.

## Sources

- This maternal-transmission recurrence and its endpoint classification are derived directly from the stated life cycle. Cytoplasmic incompatibility requires a separate paternal-dependent model.
