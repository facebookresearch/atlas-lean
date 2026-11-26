# First-order reaction and diffusion in a catalyst slab

Consider an isothermal catalyst slab of thickness $2L$, $L > 0$, with end effects neglected, effective diffusivity $D_A > 0$ and an
irreversible first-order reaction with rate constant $k \ge 0$. With $x$ the distance from the mid-plane and the surface
concentration $c_{As}$ fixed, let $c_A$ be twice differentiable on $[0, L]$, with derivatives taken within the interval at its ends, and
satisfy

$$D_A\,c_A'' = k\,c_A \quad \text{on } [0, L], \qquad c_A'(0) = 0, \qquad c_A(L) = c_{As}.$$

If $k > 0$, put $\Phi = L\sqrt{k/D_A}$, the Thiele modulus of the slab, whose volume-to-surface ratio is $L$. Then

$$c_A(x) = c_{As}\,\frac{\cosh(\Phi x/L)}{\cosh\Phi}, \qquad 0 \le x \le L,$$

so the problem has exactly this solution. The proof reverses the coordinate, $s = L - x$, and sets $V(s) = c_A(L - s)$ and
$I(s) = D_A\,c_A'(L - s)$; then $V' = -I/D_A$ and $I' = -kV$, the cable equations with $r_i = 1/D_A$ and $r_m = 1/k$, whose length
constant is $\sqrt{D_A/k} = L/\Phi$, and $I(L) = D_A\,c_A'(0) = 0$ is a sealed end with $V(0) = c_{As}$. If $k = 0$, then
$c_A'' = 0$ and $c_A'(0) = 0$ force $c_A \equiv c_{As}$; this branch is outside the cable result, which needs positive resistances.

## Depends on

## Proof depends on

- [Voltage profile and inlet relation for a cable with a sealed end](../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/sealed-end.md)

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 7.4.2, the slab case $q = 0$ of Equation 7.34 with its boundary conditions (pp. 370–371), the effectiveness factor in integral and flux form, Equations 7.36–7.37 (p. 371), and Table 7.3, Equation 7.40 (p. 372); the Thiele modulus, Equation 7.18.
