# Solution of the Kermack–McKendrick SIR system

Let $\beta, \gamma, N \in \mathbb{R}$. Functions $S, I, R \colon \mathbb{R} \to \mathbb{R}$ solve the
Kermack–McKendrick SIR system with transmission rate $\beta$, removal rate $\gamma$ and population
size $N$ if, at every time $t \ge 0$, they are differentiable with

$$S'(t) = -\frac{\beta S(t) I(t)}{N}, \qquad I'(t) = \frac{\beta S(t) I(t)}{N} - \gamma I(t), \qquad R'(t) = \gamma I(t),$$

where the quotient by $N$ is read as $0$ when $N = 0$.
