# Three regimes of the fastest rare-event time under small noise and many searchers

**Setting.** $N$ independent walkers in $\mathbb{R}^d$ start at $0$ and follow

$$dX^j_t = f(X^j_t)\,dt + \sqrt{2\epsilon}\,dW^j_t, \qquad j = 1,\dots,N,$$

with $f$ Lipschitz and $0$ a globally attracting fixed point of $\dot x = f(x)$. For a target $L \in \mathbb{R}^d$ and a small ball $B_\delta(L)$, let $\tau_j$ be the hitting time of $B_\delta(L)$ by walker $j$ and $\tau^N_{\mathrm{first}} = \min_j \tau_j$ the **extreme first passage time**. Freidlin–Wentzell theory gives the action $I_t(y) = \frac{1}{4}\int_0^t \|\dot y - f(y)\|^2\,ds$ and the finite-time cost $V(z,t) = \inf\{I_t(y) : y(0) = 0,\ y(t) = z\}$, with the initial point fixed at $0$ and the terminal point $z$ free. It solves the Hamilton–Jacobi equation

$$
\partial_t V(x,t) + f(x)\cdot\nabla_x V(x,t) + \|\nabla_x V(x,t)\|^2 = 0 ,
$$

and $t\mapsto V(z,t)$ is nonincreasing, since a path can first wait at the attracting point $0$ at no cost. For example, for $d=1$ and $f(x)=-x$, $V(x,t)=x^2/\big[2(1-e^{-2t})\big]$. The quasi-potential is $V(z) = \lim_{t\to\infty}V(z,t)$. Consider the distinguished limit $\epsilon \to 0^+$, $N \to \infty$ with $\Lambda = \epsilon\log N$ held fixed (limits taken with $\epsilon \to 0$ first, then $\delta \to 0$).

**Theorem.**

1. *(Labor shortage, $\Lambda \le V(L)$, i.e. $N \le e^{V(L)/\epsilon}$.)* $\epsilon\log\tau^N_{\mathrm{first}}$ concentrates at $V(L) - \Lambda$ and

$$\lim_{\delta\to 0^+}\lim_{\epsilon\to 0^+}\epsilon\log\mathbb{E}[\tau^N_{\mathrm{first}}] = V(L) - \Lambda;$$

the fastest walker follows essentially the single-walker optimal path and the mean time is the single-walker mean divided by $N$.
2. *(Balanced labor, $V(L) < \Lambda < \infty$.)* The mean extreme time stays finite and positive:

$$\mathbb{E}[\tau^N_{\mathrm{first}}] \simeq \Psi_L(\Lambda) = \inf\{t \ge 0 : V(L,t) = \Lambda\},$$

so by choosing the proportionality constant $\Lambda$ any positive value of the mean can be obtained, and the fastest walker follows the minimizer of the finite-time action $I_{\Psi_L(\Lambda)}$, which differs from the single-walker path.
3. *(Labor surplus, $\epsilon\log N \to \infty$.)* With overwhelming probability $\epsilon\log N\cdot\tau^N_{\mathrm{first}} \to \|L\|^2/4$, $\epsilon\log N\cdot\mathbb{E}[\tau^N_{\mathrm{first}}] \to \|L\|^2/4$, and the fastest path converges to the straight line from $0$ to $L$ traversed at constant speed: the drift $f$ becomes irrelevant.

## Expansion

Independence gives $\mathbb{P}(\tau^N_{\mathrm{first}} > t) = \mathbb{P}(\tau_1 > t)^N$. The probability that one walker reaches $B_\delta(L)$ by time $t$ is roughly $e^{-V(L,t)/\epsilon}$, so with $N = e^{\Lambda/\epsilon}$ walkers the first success occurs near the first time $t$ at which $V(L,t)$ drops to $\Lambda$, which is $\Psi_L(\Lambda)$. When $\Lambda < V(L)$ no finite time suffices, because even $V(L,\infty) = V(L) > \Lambda$; the walkers must wait for exponentially rare excursions and the time scale is $e^{(V(L)-\Lambda)/\epsilon}$. As $t \to 0$ the action is dominated by $\|L\|^2/(4t)$ from the noise term, giving the surplus regime. This explains why rare events in cell biology driven by large numbers of molecules (e.g. many receptors or ions) can occur on fast, deterministic-looking time scales, while the prefactor $\Lambda = \epsilon\log N$ controls the transition between regimes.

## Sources

- James MacLaurin and Jay M. Newby, "Extreme first passage times for populations of identical rare events", SIAM Journal on Applied Mathematics 85 (2025) 109–142, <https://doi.org/10.1137/23M1603054>; preprint arXiv:2309.01827 (2023), Section 4 (Regimes 1–3, Theorem 4.2, the Regime 1 lemma and Theorem 4.9), <https://doi.org/10.48550/arXiv.2309.01827>.
