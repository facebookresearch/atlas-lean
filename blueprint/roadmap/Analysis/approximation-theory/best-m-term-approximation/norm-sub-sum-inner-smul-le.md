# Best $M$-term approximation in an orthonormal basis

Let $(b_i)$ be a finite orthonormal basis and let $S$ hold the largest coefficients of $f$: $|\langle b_j, f\rangle| \le |\langle b_i, f\rangle|$ whenever $i \in S$ and $j \notin S$. Then $\sum_{i \in S} \langle b_i, f\rangle b_i$ is a best $\#S$-term approximation of $f$: for every set $T$ with $\#T \le \#S$ and all coefficients $(a_i)$,

$$\Big\|f - \sum_{i \in S} \langle b_i, f\rangle b_i\Big\| \le \Big\|f - \sum_{i \in T} a_i b_i\Big\| .$$

With the [error of keeping the coefficients on $S$](norm-sub-sum-inner-smul-sq.md), the best $M$-term error is $\sigma_M(f)^2 = \sum_{k > M} \gamma_k(f)^2$, where $\gamma_k(f)$ is the $k$-th largest of the $|\langle b_i, f\rangle|$ (R. A. DeVore, *Nonlinear approximation*, Acta Numerica 7 (1998), Section 2, (2.3) and (2.19)). The statement is for a finite orthonormal basis; DeVore states it for an orthonormal basis of a separable Hilbert space.
