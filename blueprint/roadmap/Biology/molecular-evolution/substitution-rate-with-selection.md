# Selected origination flux and its weak-selection scaling function

If each of $2N$ copies produces a mutation of a specified class with
probability $u$, and each such birth has conditional fixation probability
$\pi_N(s)$ in the model being used, the expected eventual-fixer birth
flux is $J_N(s)=2Nu\pi_N(s)$ by linearity.
The fixation probability must describe the actual background, or else
this is a stated single-mutant approximation, not an interference theorem.

For the canonical [diffusion fixation function](../population-genetics/diffusion-theory/wright-fisher-diffusion/kimura-fixation.md),
$\pi_N(s)=u_{2Ns}(1/(2N))$, the **finite-$N$ diffusion expression** is

$$\frac{J_N(s)}u=2N\frac{1-e^{-2s}}{1-e^{-4Ns}}\quad(s\ne0),
\qquad \frac{J_N(0)}u=1,$$

where the ratio notation assumes $u>0$; for $u=0$ the flux is zero.
Holding $S=4Ns$ fixed and taking $N\to\infty$ gives

$$2N\pi_N(S/(4N))\longrightarrow F(S)=\frac{S}{1-e^{-S}},
\qquad F(0)=1.$$

The function $F$ is strictly increasing, $F'(0)=1/2$,
$F(S)/S\to1$ as $S\to+\infty$, and
$F(-y)=y/(e^y-1)$ for $y>0$.
Thus the **F-based rate model** sets $k/u=F(4Ns)$; this is not the exact
finite-$N$ expression above. Their ratio is
$(1-e^{-2s})/(2s)$ when $s\ne0$.

## Depends on

- [Kimura fixation function](../population-genetics/diffusion-theory/wright-fisher-diffusion/kimura-fixation.md)

## Background

- [Neutral origin-flux identity](neutral-substitution-expected-eventual-fixer-ori.md)

## Expansion

For the limit use $2N(1-e^{-S/(2N)})\to S$; $S=0$ is separate.
For $S\ne0$, $F'(S)=[1-(1+S)e^{-S}]/(1-e^{-S})^2>0$, since
$e^S>1+S$. Taylor expansion at zero gives derivative $1/2$ and joins
the two monotone branches continuously.

The fixed-$S$ limit does not itself prove a uniform approximation over
an arbitrary distribution of fixed effects $s$ as $N$ varies.
Subsequent F-based DFE formulas explicitly define that rate model.
Nor does an expected birth flux make calendar-time substitutions Poisson.
A Poisson approximation requires a separately stated no-interference
and timescale-separation regime; $2Nu\to0$ alone does not control
mutation arrivals during polymorphic sojourns whose durations also grow.
No such process-limit result is asserted here.

## Sources

- M. Kimura, "Evolutionary rate at the molecular level", Nature 217 (1968), 624–626, <https://doi.org/10.1038/217624a0>. The limit is derived above.
