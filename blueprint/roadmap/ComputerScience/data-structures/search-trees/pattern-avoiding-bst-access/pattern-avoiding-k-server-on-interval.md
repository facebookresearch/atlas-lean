# Offline k-server on pattern-avoiding requests in the unit interval

For every fixed pattern $\pi$ there is a polynomial-time algorithm that, given $n$ requests $r_1, \dots, r_n \in [0, 1]$ whose sequence avoids $\pi$ (as a sequence of distinct reals), computes a $k$-server solution serving them in order with total movement $n^{O(1/\log k)}$, where the constant in the exponent depends on $\pi$. In contrast, for arbitrary request sequences in $[0,1]$ the optimal offline cost can be $\Theta(n/k)$.

## Proof sketch

The pattern-avoidance structure theorem decomposes the request sequence into a bounded number of monotone-like pieces at each of $O(\log k)$ scales; the servers are allotted to the pieces so that each server sweeps a piece monotonically, and the movement at each scale shrinks by a constant factor while the number of pieces grows by a constant factor, giving total cost $n^{O(1/\log k)}$.

## Depends on

- [Pattern-avoiding access sequences](pattern-avoiding-access-sequence.md)
- [The k-server problem](../../../online-algorithms/paging-and-k-server/the-k-server-problem.md)

## Proof depends on

- [Marcus–Tardos theorem on excluded permutation matrices](marcus-tardos-theorem.md)

## Sources

- Benjamin Aram Berendsohn, László Kozma, Michal Opler, "Optimization with Pattern-Avoiding Input", STOC (2024), arXiv:2310.04236.
