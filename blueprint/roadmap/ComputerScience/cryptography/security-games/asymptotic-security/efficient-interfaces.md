# Efficient interfaces

Compose an outer interactive machine $M'$ with an inner machine $M$. Only $M'$ communicates directly with the external environment. At a point in the execution, let $I$ count the interactions between $M'$ and $M$ so far, and let $T$ count only the steps of $M'$ so far, summed across invocations.

The interface $M'$ is efficient if there are a polynomial bound $t$ and a negligible function $\epsilon$ such that for every positive security parameter $\lambda$, every inner machine $M$, every environment and every point in the execution, the probability that $T>t(\lambda+I)$ is at most $\epsilon(\lambda)$. Neither $M$ nor the environment is required to be efficient. The interaction count enters the time bound, not the argument of the negligible error. This is an interface-overhead condition, not a bound on the combined running time of the two machines.

## Depends on

- [Efficient interactive machines](efficient-interactive-machines.md) (stateful invocations and the convention for counting a machine's own time)
- [Negligible advantage](negligible-adv.md)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, September 2017, §2.4.3, p. 33, Definition 2.12. <https://toc.cryptobook.us/>
