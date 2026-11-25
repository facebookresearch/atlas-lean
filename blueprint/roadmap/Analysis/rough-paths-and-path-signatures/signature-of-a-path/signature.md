# Signature of a path (iterated integrals)

Let $X$ be a path in $\mathbb{R}^\iota$ described by its velocity $v = (v^i)_{i \in \iota}$, so
that $dX^i_u = v^i(u)\,du$. For real $s \le t$ and a word $w = i_1 \cdots i_k$ in the letters
$\iota$, the iterated integral of $X$ along $w$ over $[s, t]$ is

$$S(X)^{i_1 \cdots i_k}_{s,t} = \int_{s < t_1 < \cdots < t_k < t} dX^{i_1}_{t_1} \cdots dX^{i_k}_{t_k}.$$

For arbitrary real $s, t$ it is defined recursively, with oriented integrals, by $S(X)^{\varnothing}_{s,t} = 1$ and

$$S(X)^{w i}_{s,t} = \int_s^t S(X)^{w}_{s,u}\, dX^i_u = \int_s^t S(X)^{w}_{s,u}\, v^i(u)\, du .$$

The signature of $X$ over $[s,t]$ is the whole family $w \mapsto S(X)^w_{s,t}$, read as the
coefficients of the tensor series $S(X)_{s,t} = \sum_w S(X)^w_{s,t}\, e_w$; since the integrals in the
recursion are oriented, $t < s$ is allowed, and the integral over the simplex describes $S(X)_{s,t}$
only for $s \le t$.

The definition makes sense for any velocity, an integral that does not exist being read as $0$;
the results below assume that every $v^i$ is interval integrable (an absolutely continuous path)
or continuous (a $C^1$ path).

## Sources

- I. Chevyrev and A. Kormilitzin, *A primer on the signature method in machine learning*,
  arXiv:1603.03788v2, §1.2.1, equation (3) and Definition 1.4.
- T. Lyons, *Rough paths, signatures and the modelling of functions on streams*, Proc. ICM 2014,
  arXiv:1405.4537, Definition 4.5.
