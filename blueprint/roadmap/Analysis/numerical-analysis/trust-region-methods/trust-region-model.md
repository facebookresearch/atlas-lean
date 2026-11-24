# Quadratic trust-region model

At an iterate with gradient $g$ and Hessian approximation $B$ (a linear operator, symmetric in
practice), a trust-region method uses the quadratic model

$$q(s) = g^\top s + \tfrac12\, s^\top B s ,$$

the model $m_k(d) = f(x_k) + g_k^\top d + \tfrac12 d^\top B_k d$ of the source without its constant
term. A trial step $s$ is computed by minimising $q$, exactly or approximately, over the ball
$\|s\| \le \Delta$; its *predicted reduction* is $q(0) - q(s) = -q(s)$, which is compared with the
actual reduction $f(x) - f(x + s)$ to accept the step and update $\Delta$.

## Sources

- Y. Yuan, *Recent advances in trust region algorithms*, Math. Program. 151 (2015), 249–281; https://lsec.cc.ac.cn/pub/yyx/papers/2015-MPB-151-249-281.pdf, subproblem (2.3)–(2.4) and ratio (2.7).
