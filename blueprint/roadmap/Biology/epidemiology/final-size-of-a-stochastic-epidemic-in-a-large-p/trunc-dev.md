# Contacts of generations within a cap L, centered at m per infective

For a finite set $S_0$ of initially susceptible individuals of the population $\{0, \dots, N-1\}$
($\#S_0$ of them), a real number $m$, $L \in \mathbb{N}$ and a [configuration](config.md)
$w = (w_1, w_2)$, let
$T_{m,L}(w) = \sum_{n=0}^{\#S_0} \sum_{i=0}^{L-1} G_L(w; n, i) \bigl(w_1(n, i) - m\bigr)$, where
$G_L$ is the [gate](gate.md). The gate vanishes unless $i < I_n \le L$, and the generations after
$\#S_0$ have no infectives, so $T_{m,L}(w)$ is the sum of $w_1(n, i) - m$ over the infectives
$(n, i)$ of the generations $n$ with $I_0 + \cdots + I_n \le L$: their contacts, centered at $m$ per
infective. It is $0$ for $L = 0$. Once $F + 1 \le L$, with $F$ the final size, it equals
$C - m(F + 1)$ ([centered count once all infectives count](trunc-dev-eq.md)).
