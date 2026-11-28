# Cruel and cool coordinates and greedy recovery of the cool bits

Given reduced LWE pairs and a cutoff $n_u$, the attack treats the first $n_u$ coordinates of a sparse binary secret as 'cruel', guesses them by enumeration, and then fixes the remaining 'cool' bits one at a time, keeping each bit at the value that gives the smaller residual spread.

Let $(a,b)$ range over reduced LWE pairs (rows of $(RA,Rb)$) with a sparse binary secret $s\in\{0,1\}^n$, and let $n_u\in\{0,\dots,n\}$ be a supplied cutoff. Coordinates $j\le n_u$ are *cruel* and the remaining $n_r=n-n_u$ are *cool*. For a candidate $s^*$ let $\sigma(s^*)$ be the standard deviation, over the reduced pairs, of the residuals $a\cdot s^*-b \bmod q$ represented in $(-q/2,q/2]$ (the source centres its residuals; the choice of representatives matters). A verification predicate $V$ on full candidates, evaluated on the original LWE samples, is a supplied input.

**Attack (Nolte et al.).**

1. Enumerate candidates for the cruel bits in increasing Hamming weight, with the cool bits set to $0$, ranking them by a statistic that distinguishes their residuals from uniform; the source uses the residual variance.
2. *Greedy recovery of the cool bits* (Algorithm 1): starting from a retained candidate, for each cool index $i$ in turn compute $\sigma_0=\sigma(s^*)$ with $s^*_i=0$ and $\sigma_1$ with $s^*_i=1$; keep $s^*_i=0$ if $\sigma_0\le\sigma_1$, else set $s^*_i=1$.
3. Output the resulting secret if $V$ accepts it (the source checks that it produces nearly correct original pairs, i.e. small residuals); otherwise continue the enumeration.

## Expansion

The cutoff comes from an empirical observation: after reduction the entries in the first columns of $RA$ keep a spread close to uniform, while later columns are strongly reduced, and the authors report $n_u\approx\rho^2n$ in their experiments, where their $\rho$ is the standard deviation of all entries of the reduced matrix divided by $q/\sqrt{12}$. They state as a hypothesis, validated experimentally, that for sparse enough secrets the cool entries contribute little to $a\cdot s$, so a candidate correct on the cruel bits already has visibly smaller residual spread than a random one. Standard deviation is a practical proxy for a statistical test, and simulated annealing is an alternative to the greedy pass. No cost or success guarantee is stated.

## Depends on

- [Reduced LWE pairs from lattice reduction of the sample matrix](reduced-lwe-samples.md)

## Proof depends on

None.

## Sources

- Niklas Nolte, Mohamed Malhou, Emily Wenger, Samuel Stevens, Cathy Li, François Charton, Kristin Lauter, "The Cool and the Cruel: Separating Hard Parts of LWE Secrets", AFRICACRYPT 2024, Lecture Notes in Computer Science; numbers from arXiv:2403.10328v2, Section 3 (Attack Parts 1–3, Algorithm 1, Figures 1 and 2), Section 3.1, Section 4 (Equation (5)) and Section 4.3.
