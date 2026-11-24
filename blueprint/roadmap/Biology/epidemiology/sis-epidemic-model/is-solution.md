# Solution of the SIS system

For real numbers $\beta$, $\gamma$ and $N$, functions $S, I \colon \mathbb{R} \to \mathbb{R}$ solve the
closed-population SIS system with transmission rate $\beta$, recovery rate $\gamma$ and population size $N$
if, at every time $t \ge 0$, they have two-sided derivatives with

$$S' = -\frac{\beta S I}{N} + \gamma I, \qquad I' = \frac{\beta S I}{N} - \gamma I,$$

where the quotient by $N$ is read as $0$ when $N = 0$. Nothing else is required: $S$ and $I$ need not be
nonnegative, and $S(0) + I(0)$ need not equal $N$.
