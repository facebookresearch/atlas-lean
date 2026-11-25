# Selection-bias decomposition

On a probability space, let $T$ be a measurable treatment event and $Y_0, Y_1$ integrable potential outcomes, and let the observed outcome be $Y = Y_1$ on $T$ and $Y = Y_0$ off $T$. Write $E[\,\cdot \mid T]$ for the expectation under the measure conditioned on $T$. Then the observed difference in group means equals the average treatment effect on the treated plus the selection bias:

$$E[Y \mid T] - E[Y \mid T^c] = E[Y_1 - Y_0 \mid T] + \big(E[Y_0 \mid T] - E[Y_0 \mid T^c]\big).$$

No positivity of $P(T)$ or $P(T^c)$ is needed.
