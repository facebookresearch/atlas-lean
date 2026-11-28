# Mass-action implementation of a smoothed-ReLU neural network

**Activation.** For $\eta > 0$, the smoothed ReLU is

$$\varphi_\eta(y) = \tfrac12\big(y + \sqrt{y^2 + 4\eta}\big),$$

a strictly increasing positive function that tends to $\max(0, y)$ as $\eta \to 0$.

**Proposition.** For a hard-wired feed-forward network with weights $W^\ell$ and biases $\beta^\ell$, the layered system

$$x^0_i \equiv d_i, \qquad \frac{d}{dt}x^\ell_i = \eta + \rho^\ell_i(x^{\ell-1})\, x^\ell_i - (x^\ell_i)^2, \qquad \rho^\ell_i(x^{\ell-1}) = \sum_{j=1}^{c_{\ell-1}} W^\ell_{ij}x^{\ell-1}_j + \beta^\ell_i,$$

implements the network with activation $\varphi_\eta$, from any nonnegative initial condition. It also converges from infinity in finite time and is exponentially reliable in the sense of the general theorem: for each input $d$ there are $C(d) \ge 1$ and $\lambda(d) > 0$ with $|x(t) - \mathfrak X(d)| \le C(d)\,|x(0) - \mathfrak X(d)|\,e^{-\lambda(d)t}$. The constant cannot be taken equal to $1$: with one node per layer, $W^2 = 100$, $\beta^2 = -100$ and $x(0) = (1.1, 1)$ near the fixed point, an initial error $0.1$ grows to about $3.67$ before decaying.

**Reaction network.** The system is the mass-action ODE of a network built edge by edge. For an edge from node $X'$ to node $X$, and for the node $X$ itself, use:

| role | reactions | ODE term for $x$ |
|---|---|---|
| ReLU smoothing | $H \to H + X$ | $\eta$ |
| edge weight $w = w^+ - w^-$ | $X' + W^+ + X \to X' + W^+ + 2X$, $\ X' + W^- + X \to X' + W^-$ | $(w^+ - w^-)\,x' x$ |
| node bias $b = b^+ - b^-$ | $B^+ + X \to B^+ + 2X$, $\ B^- + X \to B^-$ | $(b^+ - b^-)\,x$ |
| decay | $2X \to X$ | $-x^2$ |

Here $H, W^\pm, B^\pm$ are enzymatic species: they appear unchanged on both sides, so their concentrations (times rate constants) are the parameters. Signed weights and biases are encoded as differences of two nonnegative concentrations. The union over all edges and non-input nodes gives the system above.

## Depends on

- [Reliable activation systems implement feed-forward neural networks](reliable-activation-systems-implement-feed-forward-neural-networks.md)

## Proof sketch

For a fixed input $\rho$ the node equation $\dot x = \eta + \rho x - x^2$ has the unique nonnegative equilibrium $x^* = \varphi_\eta(\rho)$, the positive root of $x^2 - \rho x - \eta = 0$. The vector field is positive below $x^*$ and negative above, so every trajectory from $x(0) \ge 0$ converges to it. The derivative at $x^*$ is $\rho - 2x^* = -\sqrt{\rho^2 + 4\eta} < 0$, which gives exponential stability, and $x^*$ is smooth in $\rho$. The $-x^2$ term supplies $2$-polynomial decay. The vector field depends smoothly on the input, which gives the exponential feed-forward property. The general theorem then applies layer by layer. Each table row is the mass-action rate of its reactions: for example $X' + W^+ + X \to X' + W^+ + 2X$ produces $X$ at rate $w^+ x' x$.

## Sources

- David F. Anderson, Badal Joshi and Abhishek Deshpande, "On reaction network implementations of neural networks", *Journal of The Royal Society Interface* 18 (2021), rsif.2021.0031, <https://doi.org/10.1098/rsif.2021.0031>. Preprint version: arXiv:2010.13290 (2020), Section 3.2 (smoothed ReLU), Example 4.2, Proposition 4.9, Definition 5.1, Section 5.2 and Table 1, <https://doi.org/10.48550/arXiv.2010.13290>.
