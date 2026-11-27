# Approximate counting of proper colorings by Glauber sampling (Jerrum)

Let $G$ have $n$ vertices $v_0, \dots, v_{n-1}$ and maximum degree $\Delta$, let $q > 2\Delta$, fix a proper coloring $x_0$, and let $X_k$ be the proper colorings agreeing with $x_0$ off $\{v_0, \dots, v_{k-1}\}$, so $X_0 = \{x_0\}$, $X_n$ is the set $X$ of all proper colorings and $1/|X| = \prod_{k<n} |X_k|/|X_{k+1}|$. At stage $k$ run, $a$ times independently, the Glauber dynamics updating $\{v_0,\dots,v_k\}$ for $t$ steps from $x_0$, and let $W_k$ be the fraction of runs in which $v_k$ ends with color $x_0(v_k)$; let $W = \prod_{k<n} W_k$, computed with $n t a$ Glauber updates in total. If $0 < \varepsilon \le 1$, $\eta > 0$,

$$
t \ge \frac{q-\Delta}{q-2\Delta}\, n\Bigl(\log n + \log\frac{6eqn}{\varepsilon}\Bigr) \quad\text{and}\quad a = \Bigl\lceil \frac{27qn}{\eta\varepsilon^2} \Bigr\rceil,
$$

then $(1-\varepsilon)/|X| \le W \le (1+\varepsilon)/|X|$ with probability at least $1-\eta$.

## Proof sketch

By the frozen-boundary mixing bound, each stage samples within total variation $\varepsilon/(6eqn)$ of uniform on $X_{k+1}$, under which $v_k$ keeps its color with probability $|X_k|/|X_{k+1}| \ge 1/(eq)$. So each $\mathbb{E}[W_k]$ is within a factor $1 \pm \varepsilon/(6n)$ of the true ratio and at least $5/(6eq)$. A second-moment (Chebyshev) bound for the product of independent unbiased-up-to-bias estimators gives the stated accuracy.

## Depends on

- [Glauber dynamics for proper colorings with a frozen boundary](glauber-dynamics-for-colorings.md)

## Proof depends on

- [Rapid mixing of Glauber dynamics for colorings when q > 2 Delta](glauber-coloring-rapid-mixing.md)
- [Freezing one vertex keeps a 1/(eq) fraction of the colorings](frozen-vertex-coloring-ratio.md)
- [Concentration of the product estimator](../../../foundations/product-spaces-and-conditional-expectations/product-estimator-concentration.md)

## Sources

- David A. Levin and Yuval Peres, "Markov Chains and Mixing Times", 2nd ed., American Mathematical Society, 2017, Section 14.4.2, Theorem 14.14 and its proof.
