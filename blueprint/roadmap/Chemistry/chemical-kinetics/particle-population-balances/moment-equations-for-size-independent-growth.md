# Moment equations for size-independent growth

On sizes $L \ge L_0 \ge 0$ let the growth rate $G(t) \ge 0$ be independent of size and let a differentiable number density
$n(t, L)$ satisfy $\partial_t n + G\,\partial_L n = 0$ with nucleation flux $G(t)\,n(t, L_0) = B_0(t) \ge 0$. Assume that the
moments $\mu_k(t) = \int_{L_0}^\infty L^k n(t, L)\,dL$ are finite, that $\partial_t n$ has a locally uniform integrable bound with
weight $L^k$ so that differentiation under the integral is allowed, that integration by parts in $L$ is allowed, and that
$L^k n(t, L) \to 0$ as $L \to \infty$. Then

$$\mu_0' = B_0, \qquad \mu_k' = k\,G\,\mu_{k-1} + B_0 L_0^k \quad (k \ge 1).$$

At $G = 0$ a finite boundary density forces $B_0 = 0$. Smoothness and pointwise decay alone do not give finite weighted moments;
no point-mass forcing and no existence result for the equation are claimed. This is the stipulated model without particle washout.
The cited CSTR example includes an additional loss $-n/\tau$ for residence time $\tau>0$; if that term is retained,
each displayed moment equation acquires the additional term $-\mu_k/\tau$. It is not omitted from that model by this derivation.

## Depends on

## Proof depends on

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Example 10.2, the crystallization model with size-independent growth and nucleation boundary condition (p. 591).
