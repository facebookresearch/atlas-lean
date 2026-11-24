# Stationary averaging of the pair collision probability in the weak seed-bank model

Let $B$ be a random variable on $\{1, \dots, m\}$ with $b_j = \mathbb P(B = j)$, $b_m > 0$ and
$\gcd \{ j : b_j > 0 \} = 1$, and consider the [ancestral process of the weak seed-bank model](finite-n-weak-seed-bank-ancestral-chain-with-res.md)
with $N \ge 1$ individuals per generation, in which a line of residual age $0$ is relocated $B$
generations back to a uniform position and merges with any line it lands on.

1. The residual-age chain of one line (from age $r \ge 1$ go to $r - 1$; from age $0$ draw $B$ and go to
   $B - 1$) is irreducible and aperiodic on $\{0, \dots, m - 1\}$ with stationary law
   $\pi(r) = \mathbb P(B \ge r + 1)/\mathbb E B$; in particular $\pi(0) = 1/\mathbb E B$.
2. Two independent residual-age chains form an irreducible aperiodic chain with stationary law
   $\pi \otimes \pi$.
3. Two distinct lines with residual ages $(r_1, r_2)$ merge in the next step with probability
   $\sum_j b_j^2 / N$ if $r_1 = r_2 = 0$ (both are relocated and land at the same position), $b_r / N$ if
   one age is $0$ and the other is $r \ge 1$ (the relocated line lands on the line that stays), and $0$
   otherwise.
4. Averaged over $\pi \otimes \pi$, this pair collision probability is

    $$\frac{1}{N}\Bigl(\pi(0)^2 \sum_j b_j^2 + 2\,\pi(0) \sum_{r \ge 1} \pi(r)\, b_r\Bigr) = \frac{\pi(0)^2}{N} = \frac{\beta^2}{N}, \qquad \beta = \frac{1}{\mathbb E B},$$

    because $\sum_j b_j^2 + 2 \sum_r b_r \mathbb P(B > r) = \mathbb P(B = B') + \mathbb P(B \ne B') = 1$ for an
    independent copy $B'$ of $B$. For $\ell$ lines in the stationary configuration law, the probability of a
    merger in one step is $\beta^2 \binom{\ell}{2} / N + O(N^{-2})$, the $O(N^{-2})$ term coming from
    several collisions in one step.

5. The averaged value differs in general from the probability $\sum_j b_j^2 / N$ for two lines that are
   both relocated in the same step. For $B$ uniform on $\{1, 2\}$ the values are $4/(9N)$ and $1/(2N)$; for
   $B = 1$ both are $1/N$.

Part (1) follows from the balance equations $\pi(r) = \pi(r + 1) + \pi(0)\, b_{r+1}$ and
$\sum_{r \ge 0} \mathbb P(B \ge r + 1) = \mathbb E B$; aperiodicity uses the gcd condition, and the product of
two independent irreducible aperiodic finite chains is irreducible and aperiodic. If $B = 2$ almost surely,
the chain is periodic and the averaging does not describe two lines started in the same generation.

## Depends on

- [Ancestral process of the weak seed-bank model](finite-n-weak-seed-bank-ancestral-chain-with-res.md)

## Sources

- I. Kaj, S. M. Krone and M. Lascoux, "Coalescent theory for seed bank models", Journal of Applied Probability 38 (2001), 285–300, <https://doi.org/10.1239/jap/996986745>; author preprint dated 22 September 2000, Section 2, equations (5)–(6) and Lemma 1 (the stationary law $\mathrm{Mult}(\ell; \beta_1, \dots, \beta_m)$ of the configuration process with $\beta_j = \mathbb P(B \ge j)/\mathbb E B$), equation (7) (the first-order collision rate $x_1 \sum_{i < m} x_{i+1} b_i + \binom{x_1}{2} \sum_i b_i^2$ of a configuration $x$) and equation (8) (its stationary average $\beta_1^2 \binom{\ell}{2}$).
- J. Blath, A. González Casanova, N. Kurt and M. Wilke-Berenguer, "A new coalescent for seed-bank models", Annals of Applied Probability 26 (2016), 857–891, <https://doi.org/10.1214/15-AAP1106>, preprint <https://arxiv.org/abs/1411.4747>, Section 1 (the resulting rate factor $\beta^2 = 1/(\mathbb E B)^2$).
