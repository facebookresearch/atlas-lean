# Error bound for an ordered dot product with perturbed operations

Let $m \in \mathbb{N}$ and $h, x, \delta h, \delta x, \delta p, \delta a \in \mathbb{R}^m$, and let $e_x, e_h, e_p, e_a \ge 0$ with $|\delta x_k| \le e_x$, $|\delta h_k| \le e_h$, $|\delta p_k| \le e_p$ and $|\delta a_k| \le e_a$ for every $k$. Let $y = \sum_{k} h_k x_k$ be the ideal output, and let $\hat y = \hat a_m$ be the output of the zero-initialized left fold

$$\hat a_0 = 0, \qquad \hat a_{k+1} = \hat a_k + \hat p_k + \delta a_k, \qquad \hat p_k = (h_k + \delta h_k)(x_k + \delta x_k) + \delta p_k.$$

Then

$$|\hat y - y| \le e_x \sum_{k} |h_k| + e_h \sum_{k} |x_k| + m\, e_h e_x + m\, e_p + m\, e_a.$$
