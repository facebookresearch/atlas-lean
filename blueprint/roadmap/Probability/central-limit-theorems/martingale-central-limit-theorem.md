# Martingale central limit theorem for bounded increments

Let $(M_n)_{n\ge0}$ be a real martingale with respect to a filtration $(\mathcal F_n)_{n\ge0}$, with $M_0=0$ and increments $\xi_k=M_k-M_{k-1}$ bounded by a constant: $\lvert\xi_k\rvert\le c$ almost surely for all $k\ge1$. Suppose that for a constant $\sigma^2\ge0$

$$\frac1n\sum_{k=1}^n\mathbb E\bigl[\xi_k^2\bigm|\mathcal F_{k-1}\bigr]\longrightarrow\sigma^2\quad\text{in probability}.$$

Then $M_n/\sqrt n\to\mathcal N(0,\sigma^2)$ in distribution, where $\mathcal N(0,0)$ is the point mass at $0$.

## Expansion

A proof page must check the conditional Lindeberg condition, which is automatic since $\lvert\xi_k\rvert/\sqrt n\le c/\sqrt n$; prove convergence of the characteristic functions $\mathbb E\exp(iuM_n/\sqrt n)\to e^{-\sigma^2u^2/2}$, for instance by comparing $\exp(iuM_n/\sqrt n)$ with the product $\prod_{k\le n}\mathbb E[\exp(iu\xi_k/\sqrt n)\mid\mathcal F_{k-1}]$ after stopping when the conditional variance sum exceeds $(\sigma^2+1)n$; and treat $\sigma^2=0$, where $M_n/\sqrt n\to0$ in $L^2$.

## Sources

- P. Billingsley, *Probability and Measure*, 3rd ed., Wiley, 1995, Section 35.
- P. Hall and C. C. Heyde, *Martingale Limit Theory and Its Application*, Academic Press, 1980, Chapter 3.
