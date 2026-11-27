# Equality case under squared error

Let $(\Omega, \mathcal{F}, \mu)$ be a probability space and $\mathcal{G} \subseteq \mathcal{F}$ a sub-σ-algebra. For $W \in L^2(\mu)$ and $c \in \mathbb{R}$, conditioning leaves the squared-error risk at $c$ unchanged,

$$\mathbb{E}_\mu\big(\mathbb{E}_\mu[W \mid \mathcal{G}] - c\big)^2 = \mathbb{E}_\mu (W - c)^2,$$

if and only if $W = \mathbb{E}_\mu[W \mid \mathcal{G}]$ $\mu$-almost everywhere.
