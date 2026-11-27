# The Cardy weight and the vacuum action

For $c\ge40$ put $a=(c-1)/12$. With $\alpha,t\ge0$, write $K_\alpha(t)=I_0(4\pi\sqrt{\alpha t})$, where $I_0(z)=\sum_{k\ge0}(z^2/4)^k/(k!)^2$. The Cardy weight and density are

$$
V(t)=K_a(t)-2K_{a-1}(t)+K_{a-2}(t),\qquad \rho_C(t)=2\pi V(t).
$$

For $\beta>0$, the Laplace transform $2\pi\int_0^\infty K_\alpha(t)e^{-2\pi\beta t}\,dt$ is $\beta^{-1}e^{2\pi\alpha/\beta}$. The same transform with density $\rho_C$ (without an extra $2\pi$) gives $\beta^{-1}e^{2\pi a/\beta}(1-e^{-2\pi/\beta})^2$, the $S$-image of the reduced vacuum term. In particular $V(t)\ge8\pi^4t^2$ for $t\ge0$, with $V(0)=0$ and strict positivity for $t>0$.

The weighted mass is $M[g]=\int_0^\infty|g(t)|V(t)\,dt$. When absolutely convergent, the vacuum action is $g_{\mathrm{vac}}=-\int_0^\infty g(t)\rho_C(t)\,dt$.

The order-zero series above is the even-power form of the linked definition. The Laplace identity comes from integrating its nonnegative series term by term. In the second difference defining $V$, the constant and linear terms cancel. Since $c\ge40$ gives $a\ge2$, convexity of $\alpha\mapsto\alpha^k$ on $[0,\infty)$ makes every coefficient with $k\ge2$ nonnegative in (2.13). The quadratic term is $8\pi^4t^2$, which gives the lower bound for $t\ge0$.

## Depends on

- [Modified Bessel function of order zero](../../../Analysis/special-functions/elementary-transcendental-functions/modified-bessel-functions-of-the-first-kind/modified-bessel-i-zero.md).

## Sources

- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [§2.4, (2.11)–(2.16), p. 11](https://hexagonmath.org/pdf/2611.00174v1#page=11).
