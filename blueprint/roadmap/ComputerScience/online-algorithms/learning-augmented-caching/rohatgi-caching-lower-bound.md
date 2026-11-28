# Lower bound for caching with next-arrival predictions

For paging with cache size $k$ and next-arrival predictions, and for every bound $\epsilon$ on the relative error, every randomized online algorithm restricted to inputs with $\eta/\mathrm{OPT} \le \epsilon$ has competitive ratio

$$
\Omega\!\left(\log \min\left\{\frac{\epsilon}{k \log k},\; k\right\}\right),
$$

where $\eta$ is the $\ell_1$ prediction error.

## Proof sketch

Rohatgi fixes a parameter $1 \le t \le k$ and a universe of $k + t$ pages, and builds random inputs made of phases: each phase has $t$ clean pages, not requested in the previous phase, and $k - t$ stale pages chosen uniformly at random from the previous phase's pages; it consists of $3k \log k$ independent uniform requests to these $k$ pages followed by one copy of them in increasing order. Predictions point to the next time step inside a phase and to the end of the next phase on the final copy, so a prefix of the input determines the predictions, the total error is $O(nk^2 \log k)$ over $n$ phases, and $\mathrm{OPT} = \Theta(nt)$. Every deterministic algorithm misses $\Omega(t \log(k/t))$ times per phase in expectation, since it cannot tell which unseen pages are stale. Choosing $t = k^2 \log k/\epsilon$ for $k \log k \le \epsilon \le k^2 \log k$ and applying Yao's principle gives the bound.

## Depends on

- [Next-arrival predictions for paging](next-arrival-predictions.md)

## Proof depends on

- [Yao's minimax principle](../../../TheoryOfComputation/randomized-and-quantum-complexity/yao-s-minimax-principle/yao-minimax.md)

## Sources

- Dhruv Rohatgi, "Near-Optimal Bounds for Online Caching with Machine Learned Advice", SODA (2020), arXiv:1910.12172, Theorem 3 and Section 6 (Theorem 28).
