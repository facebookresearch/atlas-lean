# Morse lemma

Let $f \colon \mathbb{R}^n \to \mathbb{R}$ be a $C^\infty$ function with
$Df(0) = 0$ whose Hessian at $0$ is nondegenerate: if $v \in \mathbb{R}^n$ satisfies
$D^2 f(0)(v, w) = 0$ for all $w \in \mathbb{R}^n$, then $v = 0$. Then there exist an integer
$0 \le k \le n$, a map $\varphi \colon \mathbb{R}^n \to \mathbb{R}^n$ that is a local $C^\infty$
diffeomorphism at $0$ with $\varphi(0) = 0$, and an open set $U$ containing $0$ such that
$f(x) = f(0) + Q_k(\varphi(x))$ for all $x \in U$. Here $Q_k$ is the Morse quadratic form
$Q_k(y) = -y_1^2 - \dots - y_k^2 + y_{k+1}^2 + \dots + y_n^2$ on $\mathbb{R}^n$.

## Sources

- J. Milnor, Morse Theory, Ann. of Math. Studies 51 (1963) Lemma 2.2; M. Hirsch, Differential Topology; J. Lee, Intro to Smooth Manifolds, 2nd ed., Morse lemma; Lean states Euclidean origin finite-dimensional specialization with corrected nondegeneracy grouping `(∀ w, (fderiv (fderiv f) 0 v) w = 0) → v = 0`.
