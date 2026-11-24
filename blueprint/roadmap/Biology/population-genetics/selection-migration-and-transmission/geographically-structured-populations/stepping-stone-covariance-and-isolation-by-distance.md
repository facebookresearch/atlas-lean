# Stepping-stone covariances and isolation by distance

In the infinite one-dimensional stepping-stone model with demes of $N$ diploids at the integers, a fraction $m$ of immigrant gametes per generation, $m/2$ from each neighbour, and infinite-isoalleles mutation at rate $u$, let $f_k$ be the equilibrium probability that genes drawn from two demes $k$ steps apart are identical in state. Felsenstein (Section VII.6) derives from the general migration-matrix recursion (his equation (VII-52)) the equations, valid to first order in the small quantities $m$, $u$ and $1/N$,

$$f_k = mf_{k-1} + (1 - 2m - 2u)f_k + mf_{k+1}, \qquad k \ge 1,$$

with a separate equation for $f_0$ (his (VII-54)); the decaying solution is proportional to $\lambda^k$ with $\lambda$ the smaller root of the characteristic equation, approximately $1 - \sqrt{2u/m}$ when $u \ll m$, so that $f_k \approx f_0\exp(-k\sqrt{2u/m})$ (his (VII-58), (VII-59)). In the two-dimensional model with $m/4$ from each of four neighbours, the identity at large distance behaves as $f_k \approx c\,f_0\,e^{-k\sqrt{4u/m}}/\sqrt k$ with $c$ depending on $u$ and $m$ but not on $N$ (his (VII-60)); in both cases $f_k/f_0$ depends on $u$ and $m$ and not on $N$. The decline with distance is exponential in one dimension and exponential with an additional factor $k^{-1/2}$ in two. For the corresponding approach to fixation without mutation in a line of $n$ demes or an $n_1 \times n_2$ rectangle, Felsenstein gives the effective sizes $n^2/(\pi^2m) + Nn$ and $2n_1n_2/m + Nn_1n_2$ (his (VII-61), (VII-62)), and states that the transition to panmictic drift occurs near $Nm = n/(2\pi^2)$ in one dimension and near $Nm = 2$ in two. Equating the two terms of the displayed one-dimensional formula gives $Nm = n/\pi^2$ instead; in two dimensions, $2n_1n_2/m = Nn_1n_2$ gives $Nm = 2$, in agreement with the stated value.

## Depends on

- [Identity-by-descent recursion in Wright's island model](../../../../Biology/population-genetics/wright-s-island-model/island-step.md)

## Expansion

1. The general migration-matrix identity recursion and its reduction to the nearest-neighbour stepping-stone model.
2. The first-order difference equations and the decaying root in one dimension, with the condition $u \ll m$.
3. The two-dimensional asymptotics with the $k^{-1/2}$ factor.
4. The rates of approach to fixation in finite lines and rectangles, and the transition values of $Nm$, including the factor-two difference between Felsenstein's one-dimensional value and the crossing of the displayed terms.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics*, course text, University of Washington, Section VII.6, equations (VII-52)–(VII-62).
- Original result: M. Kimura and G. H. Weiss, The stepping stone model of population structure and the decrease of genetic correlation with distance, Genetics 49 (1964), 561–576. <https://doi.org/10.1093/genetics/49.4.561> The analysis of the infinite stepping-stone models follows Felsenstein (Section VII.6), who credits it to Kimura and Weiss.
