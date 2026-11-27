# Gas reservoir material balance

For an isothermal gas reservoir of fixed pore volume with gas deviation factor $z(p) > 0$ and initial pressure $p_i > 0$, let
$R = (p/z)/(p_i/z_i)$. With no water influx, a cumulative production $G_p$ from initial gas in place $G$ satisfies
$G_p = G(1 - R)$. With water influx $W_e$, in units where the initial pore volume equals $G$, the balance is
$G_p = G(1 - R) + R\,W_e$ with $0 \le W_e < G$. Pressure and production data alone then need not determine $G$: on $t \in [0, 1]$
the history $R = 1/(1 + t)$, $G_p = t/(1 + t)$ fits both $G = 1$, $W_e = 0$ and $G = 3/4$, $W_e = t/4$, and both leave a positive
volume of gas. This is a witness for this influx model, not a claim about every pressure history. Equations of state for $z$ are
outside this result.

## Depends on

## Proof depends on

## Sources

- T. A. Blasingame, PETE 613 lecture 5, *Gas Material Balance*, Texas A&M University, 2005, slides 2–5 (dry-gas $p/z$ balance and the general balance with water influx), <https://blasingame.engr.tamu.edu/z_zCourse_Archive/P613_05A/z_Ted/>.
