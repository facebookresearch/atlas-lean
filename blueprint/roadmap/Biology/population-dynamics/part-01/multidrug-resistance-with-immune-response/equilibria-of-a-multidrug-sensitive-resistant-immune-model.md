# Equilibria of a multidrug sensitive–resistant–immune model

**Model.** Let $s, r$ be the densities of antibiotic-sensitive and antibiotic-resistant bacteria (scaled by the carrying capacity), $b$ the immune-cell density (scaled by its maximal recruitment per bacterium), and $a_i$ the scaled concentration of antibiotic $i = 1,\dots,n$. With positive parameters,

$$\begin{aligned}
\dot s &= \beta_S\, s\,(1 - s - r) - \eta\, s\, b - s \sum_{i=1}^n (\alpha_i + d_i)\, a_i,\\
\dot r &= \beta_R\, r\,(1 - s - r) - \eta\, r\, b + s \sum_{i=1}^n \alpha_i\, a_i,\\
\dot b &= k\, b\,\Big(1 - \frac{b}{s + r}\Big),\\
\dot a_i &= \mu_i (1 - a_i), \qquad i = 1,\dots,n,
\end{aligned}$$

where $\beta_R = (1-c)\beta_S$ with fitness cost $0 < c < 1$, $\eta$ is the immune killing rate, $\alpha_i$ the rate at which antibiotic $i$ induces resistance, $d_i$ its killing rate of sensitive bacteria, $k$ the immune recruitment rate and $\mu_i$ the drug uptake rate. The region $\Omega = \{0 \le s, r;\ 0 \le b \le s + r \le 1;\ 0 \le a_i \le 1\}$ is positively invariant.

Set

$$A = \frac{\beta_S - \sum_i (\alpha_i + d_i)}{\beta_S + \eta},\qquad B = \frac{\beta_R}{\beta_R + \eta},\qquad C = \frac{\sum_i \alpha_i}{\beta_R + \eta}.$$

**Equilibria.** In $\Omega$ the system always has $E_0 = (0,0,0,1,\dots,1)$, $E_1 = (0,1,0,1,\dots,1)$ and the resistant-only equilibrium $E_2 = (0, B, B, 1,\dots,1)$. When $A > B$ there is also the coexistence equilibrium

$$E_3 = \Big(\frac{A(A-B)}{A - B + C},\ \frac{AC}{A-B+C},\ A,\ 1,\dots,1\Big).$$

**Stability.** $E_0$ and $E_1$ are unstable. If $A < B$, $E_2$ is locally asymptotically stable, and for the planar reduction $s = 0$, $a_i = 1$ it is globally asymptotically stable on $0 < b(0) \le r(0) \le 1$ ($E_0$ and $E_1$ lie in $\Omega$ and the face $\{b = 0\}$ is invariant, so $E_2$ does not attract all of $\Omega$). If $A > B$, $E_3$ is locally asymptotically stable, and $E_2$ is unstable; the stability regions of $E_2$ and $E_3$ are disjoint.

## Depends on

- [Explicit solution of the logistic equation](../../logistic-growth-equation/logistic.md)

## Proof depends on

- [Routh–Hurwitz: a real 2 × 2 matrix is Hurwitz iff tr M < 0 < det M](../../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/is-hurwitz-iff-trace-neg-and-det-pos.md)
- [Poincaré–Bendixson theorem](../../../../Dynamics/low-dimensional-dynamics/poincar-bendixson-theorem/poincare-bendixson.md)

## Expansion

The drug equations decouple and give $a_i \to 1$. At equilibrium, $\dot b = 0$ forces $b = 0$ or $b = s + r$. With $b = 0$ the bacteria-only equilibria are $E_0$, $E_1$ and a point with $s$ and $r$ of opposite signs, which lies outside $\Omega$. With $b = s + r$, setting $s = 0$ gives $r = b = B$, while $s > 0$ forces $b = A$ from the first equation, and the second equation then splits $A$ into the stated $s$ and $r$, which are positive exactly when $A > B$. At $E_0$ and $E_1$ the Jacobian has positive eigenvalues ($\beta_R$ and $k$ respectively). At $E_2$ the Jacobian is block triangular; one eigenvalue is $(\beta_S + \eta)(A - B)$ and the remaining $2\times 2$ block satisfies the Routh–Hurwitz conditions, so $E_2$ is stable iff $A < B$. Global stability of $E_2$ uses the planar reduction with $s = 0$, $a_i = 1$, a Dulac function to exclude periodic orbits, and Poincaré–Bendixson. Biologically, $A < B$ means the drugs push the effective growth of sensitive bacteria below that of resistant ones, and treatment leaves a purely resistant infection held at $B$ by immunity.

## Sources

- B. Daşbaşı, İ. Öztürk, "Mathematical modelling of bacterial resistance to multiple antibiotics and immune system response", SpringerPlus 5 (2016) 408, Equations (1)–(4), (9), (13) and Propositions 1, 2, 4, 6 and 7, <https://doi.org/10.1186/s40064-016-2017-8>, PMCID PMC4820433.
