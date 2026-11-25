# Compensated and exponential martingales of a Poisson process

On a probability space let $N_t$ be a [Poisson process](is-poisson-process.md)
of rate $r\ge0$, and use its natural filtration
$\mathcal F_t=\sigma(N_u:0\le u\le t)$.
For every real $\theta$, the following are integrable martingales:

$$N_t-rt,\qquad (N_t-rt)^2-rt,\qquad
 \exp\bigl(\theta N_t-rt(e^\theta-1)\bigr).$$

The zero-rate case gives the constant processes zero, zero and one.

## Depends on

- [Poisson process with independent increments](is-poisson-process.md)

## Background

- [Independent increments for the exponential-waiting-time construction](has-law-count-increments.md)

## Expansion

For $0\le s\le t$, the increment $D=N_t-N_s$ is independent of any
finite set of past coordinates by the independent-increment property.
A monotone-class argument extends this to $\mathcal F_s$.
It has Poisson mean $\mu=r(t-s)$, variance $\mu$, and
$\mathbb E e^{\theta D}=\exp(\mu(e^\theta-1))$.
With $Z=N_s-rs$ and $E=D-\mu$, conditional expectations give
$\mathbb E E=0$ and $\mathbb E E^2=\mu$; expand $(Z+E)^2$ to obtain
the second martingale, and multiply the independent exponential factors
to obtain the third. Poisson second and exponential moments give all
required integrability. The natural filtration is not arbitrarily
enlarged with future information.

In a unit-pair-rate Kingman clock construction, each fixed pair's Poisson
clock has compensator $t$, and while a fixed configuration has $b$ blocks
the superposed candidate pair clocks have rate $\binom b2$.
The number of actual coalescences over a changing block-count trajectory
is not a homogeneous Poisson process with one fixed rate; its compensator
requires the state-dependent integral and a separate argument.

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th edition (2019), <https://services.math.duke.edu/~rtd/PTE/PTE5_011119.pdf>, Section 3.7, for independent Poisson increments. The conditional-moment calculations and clock-scope qualification are derived above.
