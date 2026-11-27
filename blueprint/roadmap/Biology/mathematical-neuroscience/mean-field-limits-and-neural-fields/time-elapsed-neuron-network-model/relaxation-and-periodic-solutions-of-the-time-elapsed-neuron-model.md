# Relaxation and periodic solutions of the time-elapsed neuron model

**Model.** Let $n(s,t)$ be the probability density of neurons whose last discharge was $s$ time units ago. With a firing rate that switches on after a refractory threshold depending on the network activity,

$$
\partial_t n + \partial_s n + \mathbf{1}_{\{s \ge \sigma(N(t))\}}\, n = 0, \qquad N(t) = n(0,t) = \int_{\sigma(N(t))}^\infty n(s,t)\,ds,
$$

with initial density $0 \le n^0 \le 1$, $\int n^0 = 1$. Here $N(t)$ is the total firing rate and $\sigma(\cdot) \in (0,1)$ is the threshold; $\sigma' \le 0$ models excitatory coupling.

**Results.**
1. *(Uncoupled network.)* If $\sigma \in (0,1)$ is constant, the solution converges exponentially in $L^1$ to the stationary state

$$
A(s) = N^* e^{-(s - \sigma)_+}, \qquad N^* = \frac{1}{1 + \sigma},
$$

i.e. $\int_0^\infty |n(s,t) - A(s)|\,ds \le C e^{-\mu t}\int_0^\infty |n^0 - A|\,ds$ for some $C, \mu > 0$. Moreover $N(t) \to N^*$ exponentially, and $N(t) - N^*$ changes sign: every interval of length $\sigma$ contains a time with $N(t_0) = N^*$.
2. *(Weak excitatory coupling.)* Assume $0 \le -\sigma'(x) \le m < 1$, so that $N(t)$ is uniquely defined, and let $\bar N \in (0,1)$ be the unique solution of $\bar N(1 + \sigma(\bar N)) = 1$. If $\sigma(x) \le \sigma^+ < 1 - m\bar N$, then $N(t) \to \bar N$ exponentially fast. For $t \ge \sigma^+$ the firing rate satisfies the delay equation

$$
N(t) + \int_{t - \sigma(N(t))}^{t} N(s)\,ds = 1 .
$$

3. *(Strong coupling: periodic solutions.)* For $\alpha > 0$ let

$$N^-(\alpha) = \frac{1}{2e^\alpha - 1} < N^+(\alpha) = \frac{e^\alpha}{2e^\alpha - 1} < 1,$$

and take the Lipschitz continuous threshold

$$\sigma_\alpha(x) = \begin{cases} 2\alpha, & 0 \le x \le N^-(\alpha),\\ 2\alpha - \ln x + \ln N^-(\alpha), & N^-(\alpha) \le x \le N^+(\alpha),\\ \alpha, & x \ge N^+(\alpha),\end{cases}$$

which takes values in $[\alpha, 2\alpha]$ (so it leaves $(0,1)$ when $\alpha > 1/2$) and has $\sup|\sigma_\alpha'| = 2e^\alpha - 1 > 1$ on $[N^-(\alpha), N^+(\alpha)]$, so the weak-coupling hypothesis of item 2 fails. With $\sigma = \sigma_\alpha$, the $\alpha$-periodic function $N(t) = N^+(\alpha)e^{-t}$ on $(0,\alpha)$, which jumps from $N^-(\alpha)$ to $N^+(\alpha)$ once per period, together with the solution of the linear transport equation $\partial_t n + \partial_s n + \mathbf 1_{\{s \ge \sigma_\alpha(N(t))\}}n = 0$, $n(0,t) = N(t)$, obtained by characteristics, solves the model: $\int_{\sigma_\alpha(N(t))}^\infty n(s,t)\,ds = N(t)$ and $\int_0^\infty n(s,t)\,ds = 1$ for all $t$. Further families, with two discontinuities per period, are constructed in the same way.

## Proof sketch

Integrating the transport equation along characteristics gives $n(s,t) = N(t-s)$ for $s < \sigma$, so mass conservation $\int n = 1$ becomes the renewal identity $N(t) + \int_{t-\sigma}^{t} N = 1$: every neuron is either just firing or inside its refractory window. For constant $\sigma$ this linear delay equation has characteristic roots with negative real parts, which gives exponential relaxation and the forced oscillation of $N$ around $N^*$. Excitatory coupling shortens the refractory period when activity is high; as long as this feedback is weaker than the restoring effect of the delay ($m\bar N < 1 - \sigma^+$), the steady state still attracts. Strong coupling allows neurons to fire in synchronized volleys, producing the self-sustained oscillations seen numerically.

## Related topics

- [Leaky integrate-and-fire neuron](../../leaky-integrate-and-fire-neuron/README.md)

## Sources

- Khashayar Pakdaman, Benoît Perthame and Delphine Salort, "Relaxation and Self-Sustained Oscillations in the Time Elapsed Neuron Network Model", *SIAM Journal on Applied Mathematics* 73 (2013), 1260–1279, <https://doi.org/10.1137/110847962>. Preprint version: arXiv:1109.3014 (2011), Theorem 1, Proposition 2, Theorem 2, Lemma 5, Theorems 3–5, <https://doi.org/10.48550/arXiv.1109.3014>.
