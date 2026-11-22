# Explicit SIS solution

For real numbers $\beta$, $\gamma$, $N$ and $I_0$, the explicit SIS solution for the infectives with initial
value $I_0$ is the closed-form function

$$I(t) = \frac{I_0 e^{r t}}{1 + (\beta I_0 / N) \, \varphi_r(t)}, \qquad r = \beta - \gamma,$$

of a real $t$, where $\varphi_r$ is the growth integral and a ratio with denominator $0$ is taken to be $0$.
For $r \ne 0$ this is $I_0 e^{r t} / \bigl(1 + \frac{\beta I_0}{N r} (e^{r t} - 1)\bigr)$; for $\beta = \gamma$ it
is $I_0 / (1 + \beta I_0 t / N)$; for $\beta = 0$ it is $I_0 e^{-\gamma t}$; for $I_0 = 0$ it is $0$. The formula
is defined for all these inputs, but it solves the SIS system only for some of them, for instance on
$[0, \infty)$, with $S = N - I$, when $\beta \ge 0$, $N > 0$ and $I_0 \ge 0$.
