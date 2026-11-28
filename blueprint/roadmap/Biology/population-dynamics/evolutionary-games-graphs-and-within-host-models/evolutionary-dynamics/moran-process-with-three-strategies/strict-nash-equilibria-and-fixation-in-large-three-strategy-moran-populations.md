# Strict Nash equilibria and fixation in large three-strategy Moran populations

**Setting.** In a Moran process of size $N$ with three types A, B, C and frequency-dependent fitnesses $F(x,y),G(x,y),H(x,y)$ of A, B, C at frequencies $x=i/N$ of A and $y=j/N$ of B, let $Z^\pm_{ij}$ be the one-step probabilities of increasing/decreasing the number of A individuals, $A_N(x,y)=\alpha_{\lfloor Nx\rfloor\lfloor Ny\rfloor}$ the fixation probability of A, and $A_{N\setminus x^*}(x,y)$ the probability that A fixes without the A-frequency ever dropping to $x^*$. Let $\Lambda=\{(x,y):x,y\ge0,\ x+y\le1\}$.

**Theorem (drift towards A).** If there are $s>1$, $N^*$ and $x^*\in[0,1)$ such that $Z^+_{ij}/Z^-_{ij}\ge s$ for all $N\ge N^*$, $i/N>x^*$ and all $j$, then $\lim_{N\to\infty}A_N(x,y)=1$ for every $(x,y)\in\Lambda$ with $x>x^*$.

**Theorem (strict Nash equilibrium).** If the all-A state is a strict Nash equilibrium (at $x=1$, A has strictly larger payoff than any rare mutant B or C), then there is $x^*\in[0,1)$ with $\lim_{N\to\infty}A_N(x,y)=1$ for all $(x,y)\in\Lambda$ with $x>x^*$.

**Theorem (repelling A).** If instead $Z^+_{ij}/Z^-_{ij}\le s<1$ for $i/N>x^*$, or if $F(1,0)<G(1,0)$ and $F(1,0)<H(1,0)$, then $\lim_{N\to\infty}A_{N\setminus x^*}(x,y)=0$ for $x>x^*$. If $F<G$ and $F<H$ on $\{x<x^*\}$, then $\lim_{N\to\infty}A_N(x,y)=0$ for all $x<x^*$.

## Proof depends on

- [Birth–death coupling bounds for three-strategy fixation probabilities](birth-death-coupling-bounds-for-three-strategy-fixation-probabilities.md)

## Expansion

All statements reduce to one-dimensional birth–death chains by coupling: a lower comparison chain with birth/death ratio at least $s>1$ above $Nx^*$ is a random walk with drift towards $N$ there, so started at $Nx>Nx^*$ it reaches $N$ before $Nx^*$ with probability $1-O(s^{-N(x-x^*)})$. Near $x=1$ the ratio $Z^+/Z^-$ is close to $F(1,0)/\max(G(1,0),H(1,0))$, which exceeds $1$ for a strict Nash equilibrium, giving the drift region. Applied to the iterated prisoner's dilemma with the three reactive strategies always-defect, almost tit-for-tat and generous tit-for-tat, these bounds show cooperators fix with probability close to $1$ from a large region of initial frequencies once $N$ is large.

## Sources

- Eliza M. Ferreira, Armando G. M. Neves, "Fixation probabilities for the Moran process with three or more strategies: general and coupling results", arXiv:1811.09552: Theorems 6–7 (drift and strict Nash equilibria), Theorems 8–10 (repelling vertex, extinction), Theorems 11–12 and Proposition 5 (birth–death limits), Section 5 (cooperation with three strategies). <https://doi.org/10.48550/arXiv.1811.09552> Published version: Journal of Mathematical Biology 81 (2020) 277–314, <https://doi.org/10.1007/s00285-020-01510-0>.
