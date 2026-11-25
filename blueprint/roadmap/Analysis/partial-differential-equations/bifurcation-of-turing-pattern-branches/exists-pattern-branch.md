# Transversal zero (0, d₀) of G: near it, a G = 0 iff a = 0 or d = φ(a)

Let $G : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ be strictly differentiable at $(0, d_0)$ with
derivative $G'$, with $G(0, d_0) = 0$ and $\partial_d G(0, d_0) = G'(0, 1) \neq 0$ (transversality).
Then there is a function $\varphi : \mathbb{R} \to \mathbb{R}$ with $\varphi(0) = d_0$, strictly
differentiable at $0$ with derivative $-G'(1, 0)/G'(0, 1)$, such that for all $(a, d)$ near
$(0, d_0)$

$$a\, G(a, d) = 0 \iff a = 0 \ \text{or}\ d = \varphi(a).$$

This is the reduced form of the Crandall–Rabinowitz bifurcation from a simple eigenvalue: the zeros
of $\Phi(a, d) = a\, G(a, d)$ near $(0, d_0)$ are the trivial branch $a = 0$ and the branch
$d = \varphi(a)$.
