# Componentwise Jacobian remainder bound, scaled step

Let $f : \mathbb{R}^n \to \mathbb{R}^m$ be differentiable at $x$, let $\delta \in \mathbb{R}^n$, $i$ an output index and $H \in \mathbb{R}^m$, and let $\|\delta\|$ be the sup norm. Suppose the segment function $\varphi(t) = f(x + t\delta)_i$ is twice continuously differentiable on $\mathbb{R}$ with $|\varphi''(t)| \le H_i \|\delta\|^2$ for all $t \in [0, 1]$. Then

$$\big|\big(f(x + \delta) - f(x) - Df(x)\,\delta\big)_i\big| \le \frac{H_i}{2}\, \|\delta\|^2.$$
