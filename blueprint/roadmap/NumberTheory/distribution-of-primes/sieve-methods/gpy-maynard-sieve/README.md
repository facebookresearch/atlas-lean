# GPY–Maynard sieve

The Goldston–Pintz–Yıldırım (GPY) method finds several primes among $n + h_1, \dots, n + h_k$, for an admissible set $\{h_1, \dots, h_k\}$, by showing that the sum $\sum_n (\sum_i \mathbf 1_{\mathbb P}(n + h_i) - \rho) w_n$ is positive for non-negative Selberg-type weights $w_n$. Maynard's refinement lets the weights depend on the divisors of each $n + h_i$ separately, $w_n = (\sum_{d_i \mid n + h_i} \lambda_{d_1, \dots, d_k})^2$, which reduces the problem to the variational quantity $M_k$. The pages give the combinatorial and limiting part of that reduction and Maynard's bounds on $M_k$; the analytic input, Maynard's Proposition 4.1, enters as a hypothesis.

Positivity and the reduction:

- [Number of prime translates](prime-shift-count.md)
- [GPY detection principle, finite form](exists-lt-prime-shift-count-of-sum-pos.md)
- [GPY detection principle over dyadic ranges](infinite-lt-prime-shift-count-of-eventua.md)
- [From the asymptotics of $S_1$ and $S_2$ to infinitely many prime-rich translates](infinite-lt-prime-shift-count-of-tendsto.md)
- [Maynard's reduction for one weight profile](infinite-lt-prime-shift-count-of-maynard.md)
- [Maynard's Proposition 4.2, reduction to the asymptotics of Proposition 4.1](infinite-lt-prime-shift-count-of-lt-mayn.md)
- [Prime-rich translates give short gaps between the $j$-th and $(j+m)$-th primes](frequently-nth-prime-add-sub-le-of-infin.md)

The variational quantity:

- [Maynard's simplex](maynard-simplex.md)
- [Maynard's functional $I_k$](maynard-i.md)
- [Maynard's functional $J_k^{(m)}$](maynard-j.md)
- [Maynard's ratio](maynard-ratio.md)
- [Admissible profiles for $M_k$](is-maynard-profile.md)
- [Admissible profiles exist](exists-is-maynard-profile.md)
- [Maynard's variational quantity $M_k$](maynard-m.md)
- [$I_k$ of an admissible profile is positive](maynard-i-pos.md)
- [$M_5 > 2$](two-lt-maynard-m-five.md)
- [$M_{105} > 4$](four-lt-maynard-m-105.md)
- [Growth of $M_k$](eventually-log-sub-lt-maynard-m.md)

## Related topics

- [Selberg sieve](../selberg-sieve/README.md): the one-dimensional $\Lambda^2$ weights that the GPY and Maynard weights generalise.
- [Bounded gaps between primes](../../prime-gaps-short-intervals/bounded-gaps-between-primes/README.md): the theorems of GPY, Zhang and Maynard that this sieve proves or underlies.
- [Hardy–Littlewood prime tuples conjecture](../../prime-patterns/hardy-littlewood-prime-tuples-conjecture/README.md): admissible tuples and the conjecture that every admissible tuple has infinitely many prime translates.
- [Smooth gaps between primes](../../prime-gaps-short-intervals/smooth-gaps-between-primes/README.md): applications of the Maynard–Tao theorem in tuple form.
- [Bombieri–Vinogradov theorem](../../primes-in-progressions/bombieri-vinogradov-theorem/README.md): the level of distribution $\tfrac12$ used unconditionally.
