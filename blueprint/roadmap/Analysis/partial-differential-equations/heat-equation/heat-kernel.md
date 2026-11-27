# Fundamental solution of the heat equation

Let $E$ be a real inner product space and let $n = \dim E$ when $E$ is finite-dimensional, $n = 0$
otherwise. For every real $t$ and every $x \in E$ set

$$\Phi(t, x) = (4 \pi t)^{-n/2} \, e^{-\|x\|^2 / (4 t)}.$$

For $E$ of finite dimension $n$ (for instance $\mathbb{R}^n$) and $t > 0$ this is the fundamental solution of
the heat equation. The arguments are written in the order $(t, x)$.

The formula is defined for every $t$, with division by $0$ giving $0$ and the real power of a
negative number given by $s^a = e^{a \log |s|} \cos(\pi a)$: at $t = 0$, $\Phi(0, x)$ is $1$ for
$n = 0$ and $0$ for $n \ge 1$; for $t < 0$ it is $0$ when $n$ is odd and
$(4 \pi t)^{-m} e^{-\|x\|^2/(4t)}$ when $n = 2m$. Unlike Schmidt's Definition 4.1, it is not set to
$0$ for $t < 0$; the results about $\Phi$ assume $t > 0$.

## Sources

- M. Schmidt, *Partial Differential Equations*, lecture notes, Universität Mannheim, HWS 2025, [Chapter 4 (Heat equation)](https://www.wim.uni-mannheim.de/media/Lehrstuehle/wim/schmidt/HWS2025/chapter_4.pdf), Definition 4.1.
- L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS Graduate Studies in Mathematics 19 (2010), Chapter 2. Not consulted directly; no theorem number is cited from it.
