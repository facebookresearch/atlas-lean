# The number of blocks of a Λ-coalescent is asymptotic to the speed function

Let $\Lambda$ be a finite nonzero measure on $[0, 1]$ such that the Λ-coalescent comes down from
infinity, equivalently [Grey's condition](grey-condition.md)
$\int_1^\infty dq / \psi(q) < \infty$ holds for the [Laplace exponent](psi.md) $\psi$, and let $v$ be the
[speed of coming down from infinity](speed.md), the inverse of $u(t) = \int_t^\infty dq / \psi(q)$. Let $N_t$ be the number of
blocks at time $t$ of the [Λ-coalescent on $\mathbb N$](lambda-coalescent-on-n-as-a-time-indexed-cadlag.md) started from the partition of
$\mathbb N$ into singletons. Then

$$\lim_{t \downarrow 0} \frac{N_t}{v(t)} = 1 \quad \text{almost surely.}$$

For Kingman's coalescent, $\Lambda = \delta_0$, $v(t) = 2/t$ and this is $t N_t \to 2$. The source
normalizes $\Lambda$ to a probability measure; for a finite measure $a\Lambda$ with $a > 0$ one has
$\psi_{a\Lambda} = a \psi_\Lambda$, $u_{a\Lambda} = u_\Lambda / a$ and $v_{a\Lambda}(t) = v_\Lambda(a t)$,
while the $a\Lambda$-coalescent is the $\Lambda$-coalescent run at speed $a$, so the statement is
invariant under this scaling.

## Depends on

- [The speed of coming down from infinity](speed.md)
- [Lambda-coalescent on N as a time-indexed cadlag partition process](lambda-coalescent-on-n-as-a-time-indexed-cadlag.md)

## Expansion

A sound expansion follows the source proof: a semimartingale decomposition of $\log N_t$ whose drift is
$-\psi(N_t)/N_t$ up to a bounded error (Proposition 7 of the source), a comparison with the solution
$v$ of $v' = -\psi(v)$, and the Borel–Cantelli lemma.

## Sources

- J. Berestycki, N. Berestycki and V. Limic, "The Λ-coalescent speed of coming down from infinity", Annals of Probability 38 (2010), 207–233, <https://doi.org/10.1214/09-AOP475>, preprint <https://arxiv.org/abs/0807.4278>, Section 3, Theorem 1, equation (9), and the remark after it for $\Lambda = \delta_0$; definitions (3), (7) and (8) of $\psi$, $u$ and $v$ in Section 2; proof in Section 4.1.
