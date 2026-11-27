# Discrete Gronwall error propagation for perturbed iterations

Let $X$ be a normed space and $F : X \to X$ an $L$-Lipschitz map with $L \ge 0$. Let $x_{k+1} = F(x_k)$
and $y_{k+1} = F(y_k) + e_k$ with $\lVert e_k \rVert \le \tau$ for all $k$. Then for every $k \ge 0$,

$$\lVert y_k - x_k \rVert \le L^k \lVert y_0 - x_0 \rVert + \tau \sum_{j=0}^{k-1} L^j.$$

Consequently:

- if $L = 1 + ch$ with $c \ge 0$ and $h \ge 0$, then
  $\lVert y_k - x_k \rVert \le e^{ckh} \bigl( \lVert y_0 - x_0 \rVert + k\tau \bigr)$;
- if $0 \le L < 1$, then
  $\lVert y_k - x_k \rVert \le L^k \lVert y_0 - x_0 \rVert + \tau (1 - L^k)/(1 - L)$.

The exponential form is stated under the sufficient conditions $c, h \ge 0$, and it can fail without them:
with $L = 1/2$ (so $c = -1/2$, $h = 1$), $y_0 = x_0$ and one perturbation of size $\tau$, the error after one
step is $\tau$, larger than $e^{-1/2}\tau$.

Its instantiations for one-step integrators (the defect is $h$ times the truncation error) and for floating-point evaluation (the defect is the rounding error) are separate statements.

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, University of
  Oxford: global error of Euler's method, the recurrence $\lvert e_{n+1} \rvert \le (1 + hL)\lvert e_n
  \rvert + hT$ and its solution by induction using $1 + hL \le e^{hL}$ (the estimate preceding (20)).
  <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
