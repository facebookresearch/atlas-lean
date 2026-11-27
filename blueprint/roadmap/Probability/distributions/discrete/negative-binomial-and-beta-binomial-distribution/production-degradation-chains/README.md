# Stationary law of bursty production–degradation chains

Consider the bursty production–degradation chain on $\mathbb{N}$: bursts arrive at rate $\kappa > 0$, each adding a geometric number $B$ of molecules with mean $b \ge 0$, $P(B = j) = b^j / (1 + b)^{j+1}$ for $j \in \mathbb{N}$, and each molecule decays at rate $\gamma > 0$. Then the negative binomial law with size $a = \kappa / \gamma$ (the number of bursts per molecule lifetime) and mean $a b$ satisfies global balance for this chain: at every state $n \in \mathbb{N}$ the net probability flow into $n$ vanishes.

## Idea

In gene expression, proteins are often made in bursts: one messenger RNA yields a random number of proteins before it is degraded. A stationary law of the protein count must balance, at each state, the inflow from bursts out of lower states and from decay out of the state above against the outflow by bursts and decay. Checking this identity for the negative binomial law with size $\kappa / \gamma$ and mean $\kappa b / \gamma$ shows that it is stationary. For $b > 0$ its Fano factor, variance over mean, is $1 + b$: the mean burst size measures how far the noise exceeds Poisson noise. Without bursts, when each event adds one molecule, the immigration–death chain has the Poisson law with mean $\kappa / \gamma$ as a stationary law, with Fano factor $1$.

## Statements

- [Bursty expression stationary law](burst-death-flow-neg-binomial.md)
- [Net probability flow of the bursty production–degradation chain](burst-death-flow.md): definition used in the main statement
- [Immigration–death stationary law](immigration-death-flow-poisson.md): burst-free case: Poisson stationary law
- [Net probability flow of the immigration–death chain](immigration-death-flow.md): definition used by the burst-free case
- [Fano factor of bursty expression](fano-neg-binomial.md): Fano factor of the stationary law

## Background

- [Negative binomial distribution](../negative-binomial/README.md)

## Sources

- V. Shahrezaei and P. S. Swain, *Analytical distributions for stochastic gene expression*, Proceedings of the National Academy of Sciences of the USA, 2008.
