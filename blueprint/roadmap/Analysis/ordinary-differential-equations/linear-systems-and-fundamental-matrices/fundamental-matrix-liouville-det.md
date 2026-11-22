# Liouville's formula for the principal matrix solution

Let $n \in \mathbb{N}$, let
$A : \mathbb{R} \to \mathbb{R}^{n \times n}$ be continuous, let $t_0 \in \mathbb{R}$, write $I$ for
the $n \times n$ identity matrix, and let $\Phi : \mathbb{R} \to \mathbb{R}^{n \times n}$ satisfy
$\Phi(t_0) = I$ and $\Phi'(t) = A(t) \Phi(t)$ for every $t \in \mathbb{R}$. Then for every
$t \in \mathbb{R}$,
$\det \Phi(t) = \det \Phi(t_0) \exp\left(\int_{t_0}^{t} \operatorname{tr} A(s)\, ds\right)$.

Proof: Jacobi's formula follows from the determinant's first-order term; an integrating factor then
gives Teschl, Lemma 3.11, formula (3.91).

## Sources

- G. Teschl, Ordinary Differential Equations and Dynamical Systems, Section 3.4; https://en.wikipedia.org/wiki/Abel%27s_identity.
