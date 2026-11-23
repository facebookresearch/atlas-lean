# Morse function

Let $M$ be a $C^\infty$ manifold without boundary modelled on a real
normed space of finite dimension $d$. A function $f \colon M \to \mathbb{R}$ is a Morse function
if it is $C^\infty$ and, for every critical point $p$ of $f$ (a point where the differential
$df_p$ is zero), there exist an integer $0 \le k \le d$, a map $\varphi \colon M \to \mathbb{R}^d$
that is a local $C^\infty$ diffeomorphism at $p$ with $\varphi(p) = 0$, and an open set $U$
containing $p$ such that $f(q) = f(p) + Q_k(\varphi(q))$ for all $q \in U$. Here $Q_k$ is the
Morse quadratic form $Q_k(y) = -y_1^2 - \dots - y_k^2 + y_{k+1}^2 + \dots + y_d^2$ on
$\mathbb{R}^d$.
