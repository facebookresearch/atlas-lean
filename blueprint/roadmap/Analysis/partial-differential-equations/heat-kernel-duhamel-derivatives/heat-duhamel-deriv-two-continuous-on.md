# Heat Duhamel deriv two continuous On

Write $P_hg(x)$ for the whole-line Gaussian heat evolution, with $P_hg=g$
when $h\le0$, and

$$
D_\nu f(t,x)=\int_0^t P_{\nu(t-s)}(f(s,\cdot))(x)\,ds.
$$

A field $g$ has uniform exponential growth on $[0,T]$ when there exist
$M,c\ge0$ such that $|g(s,x)|\le M e^{c|x|}$ for every $s\in[0,T]$ and
$x\in\mathbb R$. Different fields may have different constants.

Suppose $f,f_x,f_{xx}:[0,T]\times\mathbb R\to\mathbb R$ are jointly continuous,
each has uniform exponential growth, and their ordinary spatial derivatives satisfy
$\partial_x f(s,x)=f_x(s,x)$ and $\partial_x f_x(s,x)=f_{xx}(s,x)$ for every
$s\in[0,T]$, $x\in\mathbb R$. No time derivative of these fields is assumed.

For $\nu\ge0$ and $T\ge0$, the actual second spatial derivative field
$(t,x)\mapsto\partial_{xx}D_\nu f(t,x)$ is jointly continuous on
$[0,T]\times\mathbb R$, including initial time.

The construction and spatial transfer argument are those of
[Stanford Math 220B, *Heat Equation*, §2.7.2](https://web.stanford.edu/class/math220b/handouts/heateqn.pdf).
The formal result extends the reference's compact-support hypotheses using Gaussian
exponential domination; its weaker time regularity is justified directly.
