# Integrating damped total-influence weights over the noise parameter

Let $E$ be a finite set, $A$ a real number and $c$ a real-valued function on the subsets of $E$. Then

$$\int_0^1 \sum_{\emptyset \ne S \subseteq E} 4 \lvert S\rvert\, \frac{A^{\lvert S\rvert - 1}}{A}\, (1 - u)^{\lvert S\rvert - 1}\, c(S)\, du = 4 \sum_{\emptyset \ne S \subseteq E} \frac{A^{\lvert S\rvert - 1}}{A}\, c(S),$$

where $A^{k}/A$ is read as $0$ when $A = 0$. With $A = 4p(1-p)$ and $c(S) = \hat f(S)^2$ this integrates the damped total-influence weights over the noise parameter $u$.
