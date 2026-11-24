# From $x_0$, the first return is finite exactly when $x_0$ is revisited

Let $S$ be a set, $x_0 \in S$ and $\omega$ a step sequence, and consider the jump chain $Y$ started
at $x_0$. Its [visits](visit.md) to $x_0$, counting from $0$, start with $V_0 = 0$, so
$V_1 = V_1(x_0, x_0, \omega)$ is its first return to $x_0$. The first return is finite if and only
if the chain is at $x_0$ at some step after step $0$:

$$V_1 < \infty \iff Y_{n+1}(x_0, \omega) = x_0 \text{ for some } n \in \mathbb{N} .$$
