# Iterates of the stochastic gradient method

Let $\ell(w, z)$ be the loss of a parameter $w$ in a real Hilbert space at an example $z$, let $S = (z_1, \dots, z_n)$ be a sample, $(\alpha_t)_{t \ge 0}$ step sizes and $\iota : \mathbb{N} \to \{1, \dots, n\}$ an index sequence. The stochastic gradient method (SGM) starts at $w_0$ and updates

$$
w_{t+1} = w_t - \alpha_t\, \nabla_w \ell(w_t, z_{\iota(t)}) .
$$

Here $\nabla_w \ell(w, z)$ is taken to be $0$ at points $w$ where $\ell(\cdot, z)$ is not differentiable. Each step is the gradient update of the loss at one example of the sample; the index sequence is random in the algorithm ([random selection rule](index-measure.md)) and fixed here.

## Sources

- M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Section 3 (the stochastic gradient update $w_{t+1} = w_t - \alpha_t \nabla_w f(w_t; z_{i_t})$).
