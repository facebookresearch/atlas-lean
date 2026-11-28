# Simpson index under fluctuating selection and immigration

A local community of $J$ individuals of $S+1$ species evolves by a Moran process with immigration from a metacommunity with species proportions $p_t=(p_t^1,\dots,p_t^{S+1})$; the immigration probability $m^J_t$ and the selective advantages $s^{i,J}_t$ are Markov jump processes (random environment). Under weak selection and rare immigration, $Js^{i,J}_t\to s^i_t$ and $Jm^J_t\to m_t$, and with time sped up by $J^2$ the species proportions $X_t=(X^1_t,\dots,X^{S+1}_t)$ converge in law to the solution of

$$ dX^i_t=\Big[m_t(p^i_t-X^i_t)+X^i_t\Big(s^i_t-\sum_k s^k_tX^k_t\Big)\Big]dt+\big(\sigma(X_t)\,dB_t\big)_i,\qquad (\sigma\sigma^{\top})_{ij}=2x^i(\delta_{ij}-x^j). $$

**Proposition.** The Simpson index $\mathscr S_t=\sum_{i=1}^{S+1}(X^i_t)^2$ (the probability that two randomly chosen individuals belong to the same species) satisfies

$$ d\mathscr S_t=\Big[2(1-\mathscr S_t)-2\sum_i s^i_tX^i_t(\mathscr S_t-X^i_t)+2m_t\Big(\sum_i p^i_tX^i_t-\mathscr S_t\Big)\Big]dt+dM_t $$

with $M$ a martingale: the three drift terms are neutral drift towards monodominance, a selection term, and an immigration term pulling towards the metacommunity overlap $\sum_ip^iX^i$. For two species without immigration and with $|s_t|<2$ the drift of $\mathscr S_t$ is nonnegative (Comment 1); for $S+1$ species without immigration this holds when all $|s^i_t|<1/2$ (Proposition 19); in the two-species case with $m=0$ and $\|s\|_\infty<2$, $E[\mathscr S_t]$ is increasing.

For two species, $X=X^1$ and $\mathscr S=X^2+(1-X)^2$, so $E\mathscr S_t=1-2M_1(t)+2M_2(t)$ with $M_j(t)=E[X_t^j]$, and Itô's formula gives the moment hierarchy

$$ \frac{d}{dt}M_j=j(j-1+m_tp_t)M_{j-1}+j(s_t-(j-1)-m_t)M_j-js_tM_{j+1},\qquad M_0=1. $$

Truncating at order $n$ (dropping the last selection term) gives a closed tridiagonal linear system whose $j$-th coordinate converges, as $n\to\infty$, to $E[X^j_t]$ for each fixed $j$, with error at most $\sqrt n\,\|s\|_\infty^{n-1}/(n-1)!$; this approximates the expected Simpson index forward in time at a controlled rate.

## Expansion

Itô's formula for $(X^i)^2$ gives $2X^i\,dX^i+2X^i(1-X^i)\,dt$; summing over species, the quadratic-variation terms add to $2(1-\mathscr S)$, the selection terms to $2\sum_is^i(X^i)^2-2\mathscr S\sum_ks^kX^k$, and the immigration terms to $2m(\sum_ip^iX^i-\mathscr S)$. The moment equations are not closed because selection raises the degree by one; the truncation error is controlled by bounding the neglected term $ns\,E[X^n(1-X)]$, which is small for large $n$, propagated through the truncated system with uniformly bounded symmetrized eigenvalues.

## Sources

- A. Personne, A. Guillin and F. Jabot, "On the Simpson index for the Moran process with random selection and immigration", arXiv:1809.08890 (2018), <https://doi.org/10.48550/arXiv.1809.08890>. Theorem 3 (diffusion approximation), Proposition 4 (Simpson index equation), Theorem 5 (moment truncation and error bound), Proposition 11 (monotonicity without immigration), Comment 1 and Proposition 19 (sign of the drift). Published version: International Journal of Biomathematics 13 (2020) 2050046, <https://doi.org/10.1142/s1793524520500461>.
