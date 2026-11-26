# Last iterates of p-SCLI methods converge no faster than 1/sqrt(T)

For smooth convex-concave saddle point problems (equivalently smooth monotone variational inequalities), every first-order method in the class of $1$-stationary canonical linear iterative methods, which includes the extragradient method and optimistic gradient descent-ascent with constant step size, has last iterate whose gap is $\Omega(1/\sqrt T)$ after $T$ iterations on some bilinear instance, while the averaged iterate converges at rate $O(1/T)$.

## Proof sketch

Restrict to bilinear games $\min_x \max_y x^\top A y$, on which such methods act as fixed linear maps of the iterate. Their spectral properties are governed by a polynomial in the singular values of $A$; choosing singular values spread over $[1/T, 1]$ forces some eigencomponent to contract by at most $1 - O(1/\sqrt T)$ factors per step, giving the $\Omega(1/\sqrt T)$ lower bound on the gap of the last iterate.

## Depends on

- [Extragradient and optimistic gradient descent-ascent](extragradient-and-optimistic-gradient.md)
- [Gap function and tangent residual for monotone variational inequalities](gap-function-and-tangent-residual.md)

## Proof depends on

- [Gap function and tangent residual for monotone variational inequalities](gap-function-and-tangent-residual.md)

## Sources

- N. Golowich, S. Pattathil, C. Daskalakis, A. Ozdaglar, "Last Iterate is Slower than Averaged Iterate in Smooth Convex-Concave Saddle Point Problems", COLT 2020.
