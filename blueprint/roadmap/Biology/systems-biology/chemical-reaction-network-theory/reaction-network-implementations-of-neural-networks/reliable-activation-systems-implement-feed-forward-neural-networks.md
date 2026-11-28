# Reliable activation systems implement feed-forward neural networks

**Setting.** A hard-wired feed-forward neural network has layers $\ell = 0, \dots, m$ with $c_\ell$ nodes, weight matrices $W^\ell$, biases $\beta^\ell$ and a monotone continuous activation $\varphi : \mathbb R \to \mathbb R_{\ge 0}$ applied coordinatewise; on input $d$ its layer outputs are $a^0 = d$ and $a^\ell = \varphi(W^\ell a^{\ell-1} + \beta^\ell)$. Consider the layered ODE system

$$x^0_i(t) \equiv d_i \ \ (d \in \mathbb R^{c_0}_{\ge 0}), \qquad \frac{d}{dt}x^\ell_i = f^\ell_i\big(x^{\ell-1}(t), x^\ell_i(t)\big), \quad \ell = 1, \dots, m,$$

with $x^\ell \in \mathbb R^{c_\ell}_{\ge 0}$. The system *implements* the network if for every input $d$ and every nonnegative initial condition the unique solution satisfies $x^\ell(t) \to a^\ell(d)$ for all $\ell$.

For a parametrised scalar system $\dot x = f(y, x)$ with forcing $y$:

- it is *reliable* if there is a $C^1$ map $\mathfrak X$ with $x(t) \to \mathfrak X(y)$ from every $x(0) \ge 0$;
- it has *$q$-polynomial decay* if for each compact set of $y$ there are $M, c > 0$ with $f(y, x) \le -c x^q$ for $x > M$;
- it is *exponentially feed-forward* if $y(t) \to \hat y$ exponentially fast implies $x(t) \to \hat x$ exponentially fast;
- it is *exponentially reliable* if it is reliable and there are $C(y) \ge 1$ and $\lambda(y) > 0$ with $|x(t) - \mathfrak X(y)| \le C(y)\,|x(0) - \mathfrak X(y)|\,e^{-\lambda(y)t}$ for every $x(0) \ge 0$ (for the layered system, with $|\cdot|$ a norm on all coordinates);
- it *converges from infinity in finite time* if after a time $T(y)$, independent of $x(0)$, all trajectories lie in a fixed compact set.

**Theorem.** Suppose each node equation $\dot x = f^\ell_i(y, x)$ is reliable, has $q$-polynomial decay for some $q > 1$, and is exponentially feed-forward. Then the whole layered system converges from infinity in finite time and is exponentially reliable. In particular, if each node's fixed point is $\mathfrak X^\ell_i(y) = \varphi\big((W^\ell y + \beta^\ell)_i\big)$, the system implements the network.

## Proof sketch

Argue by induction on the layer. Layer $0$ is constant. If $x^{\ell-1}(t)$ converges exponentially to its limit, the exponential feed-forward property carries exponential convergence to $x^\ell_i$, and reliability fixes the limit as $\mathfrak X^\ell_i$ of the limiting input. Polynomial decay with $q > 1$ gives uniform entry into a compact set in finite time: comparison with $\dot u = -c u^q$ forces $u(t) \le 1$ once $t > ((q-1)c)^{-1}$, whatever $u(0)$. On that compact set the rates are uniform, and Grönwall's inequality propagates them through the finitely many layers, at the cost of a multiplicative constant at each layer: a layer amplifies the error it receives from the previous one, so the constant $C$ in exponential reliability cannot in general be taken equal to $1$.

## Sources

- David F. Anderson, Badal Joshi and Abhishek Deshpande, "On reaction network implementations of neural networks", *Journal of The Royal Society Interface* 18 (2021), rsif.2021.0031, <https://doi.org/10.1098/rsif.2021.0031>. Preprint version: arXiv:2010.13290 (2020), Section 4, Definitions 4.1, 4.5 and 4.7, Theorem 4.8, Proposition A.1 and Lemma A.2, <https://doi.org/10.48550/arXiv.2010.13290>.
