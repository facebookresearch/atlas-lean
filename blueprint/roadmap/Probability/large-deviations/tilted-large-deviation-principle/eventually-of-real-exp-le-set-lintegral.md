# Local lower bound for a restricted exponential integral

Let $X$ be a topological space with measurable open sets, and let measures $\mu_n$ on $X$ satisfy
the [large deviation principle](../large-deviation-principle/satisfies-ldp.md) with rate function
$I$. Let $F : X \to \mathbb{R}$ be lower semicontinuous, $U \subseteq X$ open, $x \in U$ with
$I(x) < \infty$, and $\varepsilon > 0$. Then for all sufficiently large $n$,

$$e^{n(F(x) - I(x) - \varepsilon)} \le \int_U e^{n F} \, d\mu_n .$$
