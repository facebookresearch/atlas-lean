# An interpolant in the span of the data has minimum norm

Let $w$ lie in the span of the data points $x_1, \dots, x_n$ and interpolate the labels, $\langle w, x_i\rangle = y_i$ for every $i$. Then every interpolant $w'$, with $\langle w', x_i\rangle = y_i$ for every $i$, satisfies $\lVert w\rVert \le \lVert w'\rVert$: $w$ is the minimum-norm solution of $X w = y$.

Proof: $w' - w$ is orthogonal to every $x_i$, hence to their span, which contains $w$; so $\lVert w'\rVert^2 = \lVert w\rVert^2 + \lVert w' - w\rVert^2$.

## Sources

- C. Zhang, S. Bengio, M. Hardt, B. Recht and O. Vinyals, *Understanding deep learning requires rethinking generalization*, ICLR 2017, arXiv:1611.03530, Section 5 ("simple algebra reveals that it is equivalent to the minimum $\ell_2$-norm solution of $Xw = y$").
