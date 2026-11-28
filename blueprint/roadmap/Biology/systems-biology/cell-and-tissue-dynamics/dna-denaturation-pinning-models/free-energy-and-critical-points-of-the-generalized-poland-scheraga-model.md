# Free energy and critical points of the generalized Poland–Scheraga model

**Model.** Two DNA strands of lengths $N$ and $M$ (not necessarily equal or complementary) are paired at the points of a bivariate renewal process $\tau=\{\tau_0=(0,0),\tau_1,\tau_2,\dots\}\subset\mathbb N_0^2$ with both coordinates strictly increasing. The inter-arrival law is

$$\mathbf P(\tau_1=(n,m))=K(n+m),\qquad K(n)=\frac{L(n)}{n^{1+\alpha}},\quad n\ge2,$$

with $L$ slowly varying, $\alpha\ge1$ and $\sum_{n,m\ge1}K(n+m)=1$. An inter-arrival $(1,1)$ is a base pair, and $(i,j)$ with $i+j\ge3$ is a loop with $i+j-2$ unpaired bases (possibly asymmetric). Each contact is rewarded by $e^{h}$, $h\in\mathbb R$, so the constrained partition function is

$$Z^c_{N,M,h}=\sum_{n=1}^{N\wedge M}\ \sum_{\substack{l\in\mathbb N^n\\|l|=N}}\ \sum_{\substack{t\in\mathbb N^n\\|t|=M}}\ \prod_{i=1}^ne^{h}K(l_i+t_i).$$

The free version $Z^f_{N,M,h}=\sum_{i\le N,j\le M}K_f(i)K_f(j)Z^c_{N-i,M-j,h}$ allows unbound end segments with weights $K_f(n)=\overline L(n)/n^{\overline\alpha}$. The free energy is $\mathrm F_\gamma(h)=\lim\frac1N\log Z^f_{N,M,h}$ as $N,M\to\infty$ with $M/N\to\gamma$, and it coincides with the constrained limit.

**Theorem.** Let $\alpha\ge1$ and $\gamma\ge1$.

1. The localization (denaturation) transition is at $h_c=0$: $\mathrm F_\gamma(h)=0$ for $h\le0$ and $\mathrm F_\gamma(h)>0$ for $h>0$. There is $h_{c,\gamma}\in(0,\infty]$ such that $\mathrm F_\gamma$ is real analytic on $(-\infty,0)\cup(0,h_{c,\gamma})$, and $h_{c,\gamma}$ is a non-analyticity point when finite.
2. (Critical behavior) If $\sum_nn^2K(n)<\infty$ (for instance $\alpha>2$), then $\mathrm F_\gamma(h)\sim\mathrm F_1(h)\sim c\,h$ as $h\searrow0$, with $c^{-1}=\tfrac12\sum_{n\ge2}n(n-1)K(n)$. If $\sum_nn^2K(n)=\infty$ (for instance $\alpha\in[1,2)$), then $\mathrm F_\gamma(h)\sim c_{\alpha,\gamma}\mathrm F_1(h)$ with $c_{\alpha,\gamma}\ge1$ and $\mathrm F_1(h)\sim L_\alpha(h)\,h^{1/(\alpha-1)}$, where $L_\alpha$ is slowly varying at $0$. For $\alpha=1$ this means $\mathrm F_\gamma(h)=O(h^{1/\varepsilon})$ for every $\varepsilon>0$.
3. (Transitions inside the localized phase) For fixed $\gamma$, $\mathrm F_\gamma$ is analytic at every $h>0$ where $\gamma_c(h)\ne\gamma$, and fails to be analytic where $\gamma_c(h)-\gamma$ changes sign. Here $\gamma_c(h)$ is the critical asymmetry beyond which the strand-length mismatch can no longer be absorbed by typical loops. The derivative $\mathrm F'_\gamma$ remains continuous on $(0,\infty)$.
4. (Sharp asymptotics, $\alpha>1$) For $h>0$ and $\gamma\in(1/\gamma_c(h),\gamma_c(h))$, $Z^f_{N,M,h}\sim c_{\gamma,h}N^{-1/2}\exp(N\mathrm F_{M/N}(h))$ as $M\sim\gamma N$. For $h<0$ and $\overline\alpha<(1+\alpha)/2$, $Z^f_{N,M,h}\sim K_f(N)K_f(M)/(1-e^{h})$.

## Expansion

Writing the partition function through the bivariate renewal makes the model exactly solvable. Tilting by $e^{h}$ and an exponential change of measure $e^{\langle\lambda,\cdot\rangle}$ turns the system into a defective or proper renewal, and the free energy at aspect ratio $\gamma$ is a Legendre-type transform of the boundary of the convex set $\{\lambda:\sum_{n,m}e^{\lambda_1n+\lambda_2m+h}K(n+m)\le1\}$. Near $h=0$ the expansion of this set is controlled by the second moment of $K$, which gives the linear (first-order) law when $\sum n^2K(n)<\infty$ and the $h^{1/(\alpha-1)}$ law otherwise. Inside the localized phase, when the imposed aspect ratio $\gamma$ leaves the range of typical renewal directions, the excess length condenses into one macroscopic loop. This produces extra critical points that earlier physics analyses captured only partially. Local limit theorems for bivariate renewals give the $N^{-1/2}$ prefactor and the path estimates.

## Sources

- Giambattista Giacomin, Maha Khatib, "Generalized Poland-Scheraga denaturation model and two-dimensional renewal processes", arXiv:1510.07996 (2015), Section 1 (model, eqs. for $Z^c$, $Z^f$ and $\mathrm F_\gamma$), Proposition 1.1, Theorems 1.2, 1.5 and 1.6, <https://doi.org/10.48550/arXiv.1510.07996>.
