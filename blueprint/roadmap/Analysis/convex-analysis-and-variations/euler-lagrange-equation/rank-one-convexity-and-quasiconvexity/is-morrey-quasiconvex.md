# Morrey quasiconvex functions on 2×2 matrices

A function $W : \mathbb{R}^{2 \times 2} \to \mathbb{R}$ is quasiconvex in the sense of Morrey if, for every bounded open set $\Omega \subseteq \mathbb{R}^2$, every $A \in \mathbb{R}^{2 \times 2}$, every compact $K \subseteq \Omega$ and every smooth $\varphi : \mathbb{R}^2 \to \mathbb{R}^2$ supported in $K$,

$$|\Omega|\, W(A) \le \int_\Omega W(A + D\varphi(x))\, dx,$$

where $|\Omega|$ is the Lebesgue measure of $\Omega$. For nonempty $\Omega$, $|\Omega| > 0$, and this is the average form $W(A) \le \frac{1}{|\Omega|} \int_\Omega W(A + D\varphi(x))\, dx$. For $\Omega = \emptyset$ the condition reads $0 \le 0$, while the average form is undefined. The integral is a Bochner integral, read as $0$ when $x \mapsto W(A + D\varphi(x))$ is not integrable on $\Omega$, which cannot happen for locally bounded Borel $W$.
