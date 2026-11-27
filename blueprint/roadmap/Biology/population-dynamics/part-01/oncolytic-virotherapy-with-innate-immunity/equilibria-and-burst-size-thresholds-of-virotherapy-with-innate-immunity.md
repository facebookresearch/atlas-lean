# Equilibria and burst-size thresholds of virotherapy with innate immunity

**Model.** Let $x, y, v, z \ge 0$ be the nondimensionalized densities of uninfected tumour cells, infected tumour cells, free oncolytic virus and innate immune cells (time scaled by the infected-cell death rate, densities by the tumour carrying capacity). With tumour growth rate $r > 0$, infection rate $a > 0$, burst size $b > 0$, viral clearance rate $e > 0$, immune killing rates $c, d > 0$ of infected cells and virions, immune stimulation rate $m > 0$ and immune clearance rate $n > 0$,

$$\begin{aligned}
\dot x &= r x (1 - x - y) - a x v, & \dot y &= a x v - c y z - y, \\
\dot v &= b y - a x v - d v z - e v, & \dot z &= m y z - n z .
\end{aligned}$$

The set $D = \{x, y, v, z \ge 0,\ x + y \le 1\}$ is positively invariant. Write $N = n/m$ (relative immune decay rate) and $b_{s1} = 1 + e/a$.

**Theorem (equilibria and thresholds).**

1. $E_0 = (0,0,0,0)$ is always an equilibrium and is unstable (Jacobian eigenvalues $r, -1, -e, -n$).
2. $E_1 = (1, 0, 0, 0)$ (tumour only) is always an equilibrium; it is locally asymptotically stable if $b < b_{s1}$ and unstable if $b > b_{s1}$.
3. An immune-free equilibrium with virus present exists in the interior of $D$ (first three coordinates positive) if and only if $b > b_{s1}$, and then it is unique:

    $$E_2 = \Big( \frac{e}{a(b-1)},\ \frac{r e (ab - a - e)}{a(b-1)(ab - a + re)},\ \frac{r(ab - a - e)}{a(ab - a + re)},\ 0 \Big).$$

    At $b = b_{s1}$, $E_2$ coalesces with $E_1$ (transcritical bifurcation).
4. The Jacobian at $E_2$ has the eigenvalue $m\bar y - n$ in the immune direction and three further eigenvalues, the roots of a cubic $q(\lambda) = \lambda^3 + A_1\lambda^2 + A_2\lambda + A_3$ with $A_1, A_3 > 0$ for $b > b_{s1}$. Hence $E_2$ is locally asymptotically stable whenever $\bar y < N$ (the infected-cell level is too low to sustain immune cells) and the Routh–Hurwitz condition $A_1 A_2 - A_3 > 0$ holds. The latter holds on an interval $(b_{s1}, b_{s2})$, where $b_{s2}$ is the smallest root above $b_{s1}$ of $A_1 A_2 - A_3$ as a function of $b$; the loss of this condition at a root $b_0 \ge b_{s2}$ where it changes sign transversally is a Hopf bifurcation of $E_2$.
5. Every equilibrium with $z > 0$ has $y = N$, $x = 1 - N - a v / r$ and $z = \big((b-1)N - e v\big)/(cN + dv)$, where $v > 0$ is a root of a cubic $f(v) = v^3 + a_2 v^2 + a_1 v + a_0$ with $a_0 > 0$. Since $f$ always has a negative root, there are at most two equilibria with active immunity in $D$; they exist only when the burst size is below a critical value $\bar b$ (depending on $N$ and on the relative immune killing rate $c/d$) and coalesce at $b = \bar b$. When $a_1, a_2 > 0$ there are none, and the only equilibria are $E_0, E_1, E_2$.

## Expansion

At $E_1$ the infected-cell and virus equations decouple to the block $\begin{pmatrix} -1 & a \\ b & -(a + e) \end{pmatrix}$, whose trace is negative and whose determinant $a + e - ab$ is positive exactly when $b < 1 + e/a$; the remaining eigenvalues are $-r$ and $-n$. For $z = 0$ and $v \ne 0$, the equations $a x v = y$ and $b y = v(ax + e)$ force $a(b-1)x = e$, and $r(1 - x - y) = av$ then determines $y$ and $v$, giving $E_2$. For $z \ne 0$ the immune equation forces $y = n/m$; eliminating $x$ and $z$ leaves the cubic in $v$, and $f(0) > 0$ with $f(-\infty) = -\infty$ gives a negative root, leaving at most two positive ones. Biologically: below $b_{s1}$ the virus cannot replicate fast enough and therapy fails; between $b_{s1}$ and $b_{s2}$ (when $\bar y < N$) the system settles to a tumour–virus coexistence state free of innate immune cells; larger burst sizes produce oscillations; and the innate response creates additional equilibria only for moderate burst sizes.

## Sources

- T. A. Phan and J. P. Tian, "The role of the innate immune system in oncolytic virotherapy", 2017, Section 2 (system (4), positive invariance (7), Lemma 2 and equilibria (9)–(12), stability analysis (19)–(44), Propositions 4–6, Theorems 9 and 14), <https://doi.org/10.1155/2017/6587258> (PMCID: PMC5742943).
