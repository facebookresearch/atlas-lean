# Slutsky's theorem for a random matrix times a random vector

Let $A_L$ be random $k\times m$ matrices and $Y_L$ random vectors in $\mathbb R^m$, defined on a common probability space for each $L$. If $A_L\to A$ in probability for a constant matrix $A$ and $Y_L\to Y$ in distribution, then

$$A_LY_L\longrightarrow AY\quad\text{in distribution}.$$

For $k=m=1$ this is the [scalar-multiple form of Slutsky's theorem](../../statistical-estimation/asymptotic-normality-of-maximum-likelihood/smul-of-tendsto-in-measure-const.md). The constant limit is essential: if $A_L$ converges only in distribution to a nonconstant random matrix, the product need not converge in distribution to $AY$ for any coupling.

## Expansion

A proof page must establish:

- Joint convergence $(A_L,Y_L)\to(A,Y)$ in distribution, which holds because the limit of $A_L$ is a constant.
- The continuous-mapping theorem for the continuous map $(M,y)\mapsto My$.

## Related topics

- [Slutsky's theorem (scalar-multiple form)](../../statistical-estimation/asymptotic-normality-of-maximum-likelihood/smul-of-tendsto-in-measure-const.md)

## Sources

- A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998), Chapter 2 (Slutsky's lemma and the continuous-mapping theorem).
