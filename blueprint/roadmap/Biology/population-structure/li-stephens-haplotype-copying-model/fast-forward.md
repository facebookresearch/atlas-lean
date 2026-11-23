# Forward variables of the collapsed recursion

Let $R$ be a field, $\rho, \varepsilon \in R$ and $y$ a sequence of [site observations](obs.md). The collapsed forward variables are defined by

$$\hat\alpha_0(k) = \frac{1}{K}\, e_\varepsilon(k, y_0), \qquad \hat\alpha_{t+1} = \Phi(y_{t+1}, \hat\alpha_t),$$

where $e_\varepsilon$ is the [emission weight](emit.md), $\Phi$ the [collapsed forward step](fast-step.md) and $x/0 = 0$.
