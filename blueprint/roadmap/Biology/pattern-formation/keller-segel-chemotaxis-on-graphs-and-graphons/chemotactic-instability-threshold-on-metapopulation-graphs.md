# Chemotactic instability threshold for Keller–Segel on a metapopulation graph

Let $G$ be an undirected graph on patches $1,\dots,N$ with adjacency matrix $A$, degree matrix $D$ and graph Laplacian $L=(A-D)/N$, so $(Lv)_i=\frac1N\sum_jA_{ij}(v_j-v_i)$ and $L$ has eigenvalues $\lambda_0=0>\lambda_1\ge\dots\ge\lambda_{N-1}$ when $G$ is connected. Individuals on an edge $i\sim j$ move from $i$ to $j$ with Fermi probability $\mathbb P(i\to j)=e^{\chi c_j}/(e^{\chi c_i}+e^{\chi c_j})$, where $\chi\ge0$ is the chemotactic sensitivity. The **graph Keller–Segel model** is
$$\begin{aligned}
\dot n_i&=\frac{\eta_n}{N}\sum_jA_{ij}\big(n_j\mathbb P(j\to i)-n_i\mathbb P(i\to j)\big)+f(n_i),\\
\dot c_i&=\frac{\eta_c}{N}\sum_jA_{ij}\frac{c_j-c_i}{2}+\alpha n_i-\beta c_i,
\end{aligned}$$
with $\eta_n,\eta_c,\alpha,\beta>0$ and $f(n)=nh(n)$. Assume an equilibrium $\bar n>0$ with $f(\bar n)=0$ and $f'(\bar n)<0$, and set $\bar c=\alpha\bar n/\beta$.

**Proposition.** The uniform state $(n_i,c_i)\equiv(\bar n,\bar c)$ is linearly unstable to perturbations along the eigenvector of $\lambda_k<0$ exactly when $\chi>\chi_k^*$, where

$$\chi_k^*=\frac{-\tfrac12\eta_n\eta_c\lambda_k^2+\big[\beta\eta_n-\eta_cf'(\bar n)\big]\lambda_k+2\beta f'(\bar n)}{\alpha\eta_n\bar n\,\lambda_k}>0 .$$

Hence patterns form iff $\chi>\chi^*=\min_{1\le k\le N-1}\chi_k^*$.

For a graphon $W$ on $[0,1]$ that is a nonnegative, even, $1$-periodic function $W(x-y)$, not identically zero, the graphon Laplacian $\mathcal L_WF(x)=\int_0^1W(x,y)(F(y)-F(x))\,dy$ satisfies $\mathcal L_W\cos(2\pi kx)=-[\widehat W(0)-\widehat W(k)]\cos(2\pi kx)$, where $\widehat W(k)=\int_0^1W(z)\cos(2\pi kz)\,dz$, and $\widehat W(0)-\widehat W(k)>0$ for $k\ne0$. The same threshold applies with $\lambda_k$ replaced by $-[\widehat W(0)-\widehat W(k)]$. Since $\widehat W(k)\to0$, $\chi^*(k)\to\chi^{**}$ with

$$\chi^{**}=\frac{\tfrac12\eta_n\eta_c\widehat W(0)^2+\big[\beta\eta_n-\eta_cf'(\bar n)\big]\widehat W(0)-2\beta f'(\bar n)}{\alpha\eta_n\bar n\,\widehat W(0)},$$

and if $\chi>\chi^{**}$ then infinitely many wavenumbers are unstable.

## Expansion

At the uniform state $\mathbb P(i\to j)=\tfrac12$ and $\partial\mathbb P(i\to j)/\partial c_j=-\partial\mathbb P(i\to j)/\partial c_i=\chi/4$. The Jacobian therefore has the Kronecker form $I_N\otimes P+L\otimes C$, where $P$ holds the local reaction terms and $C$ the movement terms. By the master-stability decomposition, its spectrum is the union of the spectra of the $2\times2$ matrices $P+\lambda_kC$. The trace $f'(\bar n)-\beta+\lambda_k(\eta_n+\eta_c)/2$ is always negative, so instability requires

$$\det(P+\lambda_kC)=-\Big(f'(\bar n)+\lambda_k\frac{\eta_n}2\Big)\Big(\beta-\lambda_k\frac{\eta_c}2\Big)+\lambda_k\alpha\frac{\eta_n\chi\bar n}{2}<0,$$

which rearranges to $\chi>\chi_k^*$. This is the network analogue of the classical Keller–Segel Turing condition, with Laplacian eigenvalues in place of $-|\xi|^2$. Because graphon spectra accumulate at $-\widehat W(0)$ rather than at $-\infty$, the threshold stays bounded at high wavenumber, and arbitrarily fine patterns can destabilize together.

## Sources

- Daecheol Kim, Yefei Zhang, Yuxuan Zhao, Daniel B. Cooney, "The Keller-Segel Model for Chemotaxis on Metapopulation Graphs and Graphons", arXiv:2610.31049 (2026), Section 3 (graph model, eq. for $\chi_k^*$ and $\chi^*$), Section 5.1 with Propositions 5.2–5.3, <https://doi.org/10.48550/arXiv.2610.31049>.
