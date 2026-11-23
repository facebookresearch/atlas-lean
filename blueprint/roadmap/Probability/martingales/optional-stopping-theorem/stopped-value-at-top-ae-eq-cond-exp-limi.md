# Stopped value as conditional expectation of the limit

Let $\mu$ be a probability measure
on $\Omega$, let $(\mathcal{F}_n)_{n \in \mathbb{N}}$ be a filtration, and let
$(f_n)_{n \in \mathbb{N}}$ be a real-valued martingale with respect to $(\mathcal{F}_n)$ and $\mu$
that is uniformly integrable in $L^1(\mu)$. Let $f_\infty$ be its limit process, a function
measurable with respect to $\bigvee_n \mathcal{F}_n$ to which $f_n$ converges $\mu$-almost
everywhere. Then for every stopping time $\tau$ with values in $\mathbb{N} \cup \{\infty\}$, the
value $f_\tau$ of $f$ at $\tau$ (with $f_\tau(\omega) = \lim_n f_n(\omega)$ where
$\tau(\omega) = \infty$) satisfies $f_\tau = \mu[f_\infty \mid \mathcal{F}_\tau]$ $\mu$-almost
everywhere, where $\mu[\,\cdot \mid \mathcal{F}_\tau]$ is conditional expectation given the
σ-algebra $\mathcal{F}_\tau$ of $\tau$.

For each $n$, bounded optional sampling gives
$f_{\tau \wedge n} = \mu[f_\infty \mid \mathcal{F}_{\tau \wedge n}]$ almost everywhere, and
Lévy's upward theorem for the filtration $n \mapsto \mathcal{F}_{\tau \wedge n}$ identifies the
almost-everywhere limit of these conditional expectations with
$\mu[f_\infty \mid \bigvee_n \mathcal{F}_{\tau \wedge n}] = \mu[f_\infty \mid \mathcal{F}_\tau]$.
