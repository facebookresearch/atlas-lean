# Projecting a state onto the variables of IMP

IMP has variables indexed by natural numbers and states $\mathbb{N} \to \mathbb{N}$; the imperative language with arrays has variables named by strings. Given a renaming $\rho$ from natural numbers to strings, the projection of a state $s$ of the imperative language with arrays is the IMP state $\pi_\rho(s)$ with

$$\pi_\rho(s)(n) = s(\rho(n)) \quad \text{for every } n \in \mathbb{N}.$$

Variables outside the range of $\rho$ are forgotten.
