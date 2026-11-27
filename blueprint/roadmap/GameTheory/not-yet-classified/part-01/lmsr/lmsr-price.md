# LMSR price

For a nonempty finite set of outcomes, a liquidity parameter $b$ and outstanding quantities $q$, the LMSR instantaneous price of outcome $i$ is the softmax

$$\frac{e^{q_i/b}}{\sum_j e^{q_j/b}},$$

with the uniform value $1/n$ for $n$ outcomes when $b = 0$, by the convention $x/0 = 0$.
