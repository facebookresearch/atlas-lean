# Stochastic gradient iterates of a linear model

For data points $x_1, \dots, x_n$ in a real inner product space, indices $i_t$, step sizes $\eta_t$ and scalar prediction errors $e_t$, the iterates are $w_0 = 0$ and

$$
w_{t+1} = w_t - \eta_t\, e_t\, x_{i_t} .
$$

For a linear model with loss $\ell(\langle w, x\rangle, y)$, the gradient of the loss at the example $i$ is $\ell'(\langle w, x_i\rangle, y_i)\, x_i$, so every run of stochastic gradient descent on the empirical risk from $w_0 = 0$ has this form, with $e_t = \ell'(\langle w_t, x_{i_t}\rangle, y_{i_t})$. The errors are arbitrary scalars here, which covers every loss and every choice of indices.

## Sources

- C. Zhang, S. Bengio, M. Hardt, B. Recht and O. Vinyals, *Understanding deep learning requires rethinking generalization*, ICLR 2017, arXiv:1611.03530, Section 5.
