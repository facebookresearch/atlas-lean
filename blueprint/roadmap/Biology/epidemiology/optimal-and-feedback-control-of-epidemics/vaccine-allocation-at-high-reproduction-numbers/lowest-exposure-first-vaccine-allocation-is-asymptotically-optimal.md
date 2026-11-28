# Lowest-exposure-first vaccine allocation is asymptotically optimal at high $R_0$

**Model.** A population is split into $n$ groups with population fractions $N_j>0$, $\sum_j N_j=1$. Let $C_{jk}\ge 0$ be the mean contact rate of a member of group $j$ with members of group $k$, $\sigma_j>0$ the relative susceptibility and $\eta_j>0$ the relative infectivity of group $j$ ($\sigma_1=\eta_1=1$), and set $D_{jk}=\sigma_j\eta_k C_{jk}/N_k$. A leaky vaccine multiplies susceptibility by $\varepsilon\in(0,1)$. With $S_j,V_j,I_j,R_j$ the unvaccinated-susceptible, vaccinated, infected and recovered fractions in group $j$,

$$S_j'=-\beta S_j\sum_{k}D_{jk}I_k,\qquad V_j'=-\varepsilon\beta V_j\sum_{k}D_{jk}I_k,\qquad I_j'=\beta\,(S_j+\varepsilon V_j)\sum_{k}D_{jk}I_k-\gamma I_j,\qquad R_j'=\gamma I_j .$$

Vaccination happens before the outbreak: an allocation is a vector $\vec v$ with $0\le v_j\le N_j$ and $\sum_j v_j=v$ (total coverage), and $V_j(0)=v_j$. The basic reproduction number is the spectral radius of $\frac{\beta}{\gamma}D$, and $R_0$ is varied through $\beta$ with all other parameters fixed. In the limit of a vanishing initial infection, the infected fractions $z_j$ of the groups solve the final size system

$$N_j-z_j=(N_j-v_j)\exp\Big(-\frac{\beta}{\gamma}\sum_{k}D_{jk}z_k\Big)+v_j\exp\Big(-\varepsilon\frac{\beta}{\gamma}\sum_{k}D_{jk}z_k\Big),\qquad 1\le j\le n,$$

and the attack rate is $Z(R_0,\vec v)=\sum_j z_j$. The optimal allocation problem is to minimize $Z(R_0,\vec v)$ over admissible $\vec v$ with fixed total coverage $v$.

**Exposure index.** The exposure index of group $j$ is

$$e_j=\sigma_j\sum_{k=1}^{n}C_{jk}\eta_k ,$$

proportional to the infection hazard of a member of group $j$ placed in a fully infected population.

**Lemma (survivors at high transmission).** For every admissible $\vec v$ there is $c>0$ such that, as $\beta\to\infty$,

$$\frac{1-Z(\beta,\vec v)}{\sum_{j=1}^{n}v_j\exp\big(-\varepsilon\frac{\beta}{\gamma}e_j\big)}=1+O(e^{-c\beta}).$$

**Theorem (asymptotically optimal allocation).** Order the groups so that $e_1\le e_2\le\dots\le e_n$ and let $j^*$ be the largest index with $\sum_{k\le j^*}N_k\le v$. The allocation that fills the least exposed groups first,

$$\vec v^{\,*}=\Big(N_1,\dots,N_{j^*},\;v-\sum_{k=1}^{j^*}N_k,\;0,\dots,0\Big),$$

is nearly optimal: if $\vec v_{\rm opt}$ minimizes $Z(R_0,\cdot)$, then for some $c>0$

$$E=\frac{Z(R_0,\vec v^{\,*})-Z(R_0,\vec v_{\rm opt})}{1-Z(R_0,\vec v_{\rm opt})}=O(e^{-cR_0}),\qquad R_0\to\infty .$$

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [Final-size equation (Kermack–McKendrick 1927)](../../kermack-mckendrick-sir-model/final-size-eq.md)

## Expansion

At high transmission almost every unvaccinated person is infected, so $z_k\approx N_k$ minus an exponentially small amount and the exponent in the final size system becomes $\frac{\beta}{\gamma}\sum_k D_{jk}N_k=\frac{\beta}{\gamma}e_j$. The unvaccinated survivors are then of order $e^{-\beta e_j/\gamma}$ and negligible against the vaccinated survivors $v_je^{-\varepsilon\beta e_j/\gamma}$, which gives the lemma. Up to a relative error $O(e^{-c\beta})$, minimizing $Z$ is therefore the linear program of maximizing $\sum_j v_je^{-\varepsilon\beta e_j/\gamma}$ under $0\le v_j\le N_j$, $\sum_jv_j=v$, whose solution is to allocate greedily to the largest coefficients, i.e. the lowest exposure indices; this is $\vec v^{\,*}$. The conclusion is the reverse of the low-$R_0$ intuition of vaccinating the most connected or most susceptible: at high $R_0$ those people are infected anyway (a leaky vaccine only delays them), while a dose given to a little-exposed person most often keeps that person uninfected. In the source's computations for nine age groups with United States contact data and 80% efficacy, $\vec v^{\,*}$ coincides with the computed optimum for $R_0\gtrsim 7.5$ and its relative error is below 1% for $R_0>5.7$; across other countries' contact matrices the 1% threshold falls in $4<R_0<10$.

## Sources

- Nir Gavish, Guy Katriel, "Optimal vaccination at high reproductive numbers: sharp transitions and counterintuitive allocations", Proceedings of the Royal Society B: Biological Sciences 289 (2022), 20221525, <https://doi.org/10.1098/rspb.2022.1525>. Published version of arXiv:2202.03909, cited next; locators there refer to the arXiv version.
- N. Gavish and G. Katriel, "Optimal vaccination at high reproductive numbers: sharp transitions and counter-intuitive allocations", arXiv:2202.03909 (2022), Section 2 (exposure index and Theorem 1), Section 5 (model, final size equations in Section 5.2, Lemma 1 in Section 5.3) and Appendix A (proofs), <https://doi.org/10.48550/arXiv.2202.03909>.
