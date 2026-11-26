# Coexistence equilibria and tristability in competition between herds

**Model.** Two competing populations $Q$ and $P$ both live in herds and compete only through individuals on the herd boundaries:

$$
\frac{dQ}{d\tau} = r\Big(1-\frac{Q}{K_Q}\Big)Q - q\sqrt{P}\sqrt{Q},\qquad
\frac{dP}{d\tau} = m\Big(1-\frac{P}{K_P}\Big)P - p\sqrt{P}\sqrt{Q},
$$

with positive parameters. For $P,Q>0$ set $X=\sqrt{Q/K_Q}$, $Y=\sqrt{P/K_P}$, $t=\tau\,\frac{q\sqrt{K_P}}{2\sqrt{K_Q}}$ and

$$
a=\frac{K_Q}{K_P}\frac{p}{q},\qquad b=\frac{r\sqrt{K_Q}}{q\sqrt{K_P}},\qquad c=\frac{m\sqrt{K_Q}}{q\sqrt{K_P}},
$$

to obtain

$$
\frac{dX}{dt} = b(1-X^2)X - Y,\qquad \frac{dY}{dt} = c(1-Y^2)Y - aX.
$$

**Theorem.**

1. Trajectories are ultimately bounded.
2. Coexistence equilibria are the first-quadrant intersections of the cubics $Y=b(1-X^2)X$ and $X=\tfrac{c}{a}(1-Y^2)Y$. If $a>bc$ there is no feasible coexistence equilibrium. If $a<bc$ there is at least one, $E_3^C$, and there are one or three; the conditions $b>\tfrac{3\sqrt3}{2}$ and $c>\tfrac{3\sqrt3}{2}a$ are sufficient for three, $E_4^C,E_3^C,E_5^C$ (ordered by abscissa).
3. Every equilibrium with $X<\tfrac{\sqrt3}{3}$ or $Y<\tfrac{\sqrt3}{3}$ is unstable; hence a unique coexistence equilibrium is unstable, and with three equilibria $E_4^C$ and $E_5^C$ are unstable.
4. For an equilibrium $E_3^C$ with $X>\tfrac{\sqrt3}{3}$ and $Y>\tfrac{\sqrt3}{3}$ the Jacobian trace is negative, so $E_3^C$ is stable as soon as $bc\,(1-3X^2)(1-3Y^2)>a$; the source asserts this holds for the middle equilibrium in the three-equilibrium case.
5. In the original variables both populations can vanish: near the origin $\dot Q\sim r\sqrt Q - q\sqrt P$ and $\dot P\sim m\sqrt P - p\sqrt Q$, so joint collapse occurs from states with $\frac{m}{p}<\frac{\sqrt Q}{\sqrt P}<\frac{q}{r}$.

Consequently, when three coexistence equilibria exist the stable middle equilibrium coexists with the stable single-species states $(K_Q,0)$ and $(0,K_P)$: the system is **tristable**, with the phase plane split into three basins, in contrast with classical Lotka–Volterra competition, where stable coexistence and competitive exclusion never coexist.

## Expansion

Eliminating $Y$ gives the eighth-degree equation $cb^3X^8-3cb^3X^6+3cb^3X^4-cb(b^2+1)X^2-a+cb=0$, whose sign pattern and Descartes' rule bound the number of positive roots; comparing slopes of the two cubics at the origin gives the threshold $a=bc$. The Jacobian is $\begin{pmatrix} b(1-3X^2) & -1\\ -a & c(1-3Y^2)\end{pmatrix}$. If both coordinates are below $\sqrt3/3$ its trace is positive; if only one is, the trace and determinant conditions cannot hold together. If both exceed $\sqrt3/3$ the trace is negative and stability reduces to the determinant condition; geometrically, $E_3^C$ lies where both cubics are decreasing (so $X,Y<1$), and the determinant compares their slopes there. Item 3 is fully proved; item 4 should be read with its determinant condition.

## Sources

- D. Melchionda, E. Pastacaldi, C. Perri, E. Venturino, *Interacting population models with pack behavior*, arXiv:1403.4419 (2014). <https://doi.org/10.48550/arXiv.1403.4419> — Section 3.3 (boundary equilibria), Section 6: Propositions 13–15 and 17 and Remark 16, Section 6.2 and Conclusions (tristability).
