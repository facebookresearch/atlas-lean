# Moment equations for size-independent growth

For sizes $L > L_0 \ge 0$, fix a time $t$, with size-independent growth rate $G$ and boundary flux $B_0$ at that time. Let
$n(t,L)$ be an ordinary density, differentiable in size in the interior and continuous from the right at $L_0$, with

$$\partial_t n(t,L)+G\,\partial_L n(t,L)=0,\qquad G\,n(t,L_0)=B_0.$$

For a fixed order $k\in\mathbb{N}$, define $\mu_k(s)=\int_{L_0}^\infty L^k n(s,L)\,dL$. Assume absolute integrability at $t$ of
both $n(t,L)$ and $L^k n(t,L)$ in size, and $L^k n(t,L)\to0$ at infinity. In a neighborhood of $t$, assume time differentiability at each
interior size and a single integrable bound in size for $|L^k\partial_t n(s,L)|$. Also assume the size sections $n(s,\cdot)$
are almost-everywhere measurable for $s$ near $t$, and $\partial_t n(t,\cdot)$ is almost-everywhere measurable. These hypotheses
allow differentiation under the integral. The transport equation gives integrability of the weighted transport term, so integration
by parts yields the following formulas, each under the hypotheses for its own order:

$$\mu_0'(t)=B_0\quad(k=0),\qquad \mu_k'(t)=kG\,\mu_{k-1}(t)+B_0 L_0^k\quad(k\ge1).$$

When $G=0$, the boundary condition forces $B_0=0$ without division. If the equation instead includes a size-independent linear
loss $+\ell n(t,L)$ on the left, the same hypotheses give the additional term $-\ell\mu_k(t)$ in each moment equation. In the
cited stirred-tank model, $\ell=1/\tau$ for residence time $\tau>0$; the no-washout result sets $\ell=0$. No existence or
point-mass forcing is asserted.

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Example 10.2, the crystallization model with size-independent growth and nucleation boundary condition (p. 591).
