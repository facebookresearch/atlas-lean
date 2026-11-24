# Moments of a driving functional of Gaussian driving data

Let $T \ge 0$, $t \in [0, T]$, let $P$ be a measure on $\Omega$ and
$Z : \Omega \to \mathbb{R}^2 \times C([0, T], \mathbb{R}^2)$ a random element with a Gaussian law
under $P$, for the Borel $\sigma$-algebra, whose first component is $U_0$ and whose second component
is $M$ on $[0, T]$. Let $\Lambda$ be a continuous linear functional with

$$
\Lambda(u, f) = \langle c_0, u \rangle + \langle \ell, f(t) - f(0) \rangle +
\int_0^t \langle \kappa(s), f(s) - f(0) \rangle\, ds,
$$

and let $L_1$ be any continuous linear functional on the same space. Then, writing $E$ for integrals
against $P$,

$$
\begin{aligned}
E[L_1(Z)\, \Lambda(Z)] &= E[L_1(Z) \langle c_0, U_0 \rangle] \\
&\quad + E[L_1(Z) \langle \ell, M(t) - M(0) \rangle] \\
&\quad + \int_0^t E[L_1(Z) \langle \kappa(s), M(s) - M(0) \rangle]\, ds,
\end{aligned}
$$

by exchanging the expectation with the integral in $s$.
