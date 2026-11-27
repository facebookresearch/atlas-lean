# Reactivity of marine metapopulations in the $\ell_1$ norm and source–sink patches

**Setting.** A linear metapopulation model $x'=Ax$ on $n$ habitat patches has $A=F-V$: $F\ge0$ holds births (larvae produced on patch $j$ and settling on patch $i$), and $V$ is a nonsingular M-matrix holding deaths and adult movement. Since abundances are nonnegative, total population size is measured by the $\ell_1$ norm $\|x\|_1=\sum_ix_i$. The **reactivity** $\bar\sigma$ and **attenuation** $\underline\sigma$ are the maximal and minimal initial relative growth rates $\frac1{\|x\|}\frac{d\|x\|}{dt}\big|_{t=0}$ over nonzero initial states. Let $\lambda_j=\sum_ia_{ij}$ be the initial growth rate of the total population started from one individual on patch $j$. Let $K=FV^{-1}$ be the next-generation matrix and $R_j=\sum_ik_{ij}$ the lifetime number of offspring of an individual starting on patch $j$; patch $j$ is a **source** if $R_j>1$ and a **sink** if $R_j<1$.

**Results.**

1. (Reactivity in $\ell_1$) For nonnegative states, $\bar\sigma=\max_j\lambda_j$ and $\underline\sigma=\min_j\lambda_j$: the extreme column sums of $A$. In contrast, the $\ell_2$ reactivity is the largest eigenvalue of the symmetric part $\tfrac12(A+A^{\mathsf T})$. The two notions can disagree, so a system can be reactive in one norm and not in the other.
2. ($\mathcal R_0$ as a weighted mean) If $v$ is the right Perron eigenvector of $K$ normalized by $\sum_iv_i=1$, then $\mathcal R_0=\rho(K)=\sum_jR_jv_j$. This holds with no further assumptions.
3. (Sources drive reactivity) Suppose $V=\begin{pmatrix}V_{11}&0\\V_{21}&D\end{pmatrix}$ with $D=\operatorname{diag}(d_{k+1},\dots,d_n)>0$, i.e. individuals on patches $k+1,\dots,n$ do not migrate as adults (sedentary adults with dispersing larvae). Then $\lambda_j>0\iff R_j>1$ for $j>k$. Hence the system is $\ell_1$-reactive if some such patch is a source, and attenuating if some such patch is a sink. If $V$ is diagonal, the system is reactive iff $\max_jR_j>1$ and attenuating iff $\min_jR_j<1$.

## Expansion

The $\ell_1$ norm counts individuals, so its reactivity answers the biological question of whether the total population can initially grow. Because $\frac{d}{dt}\mathbf 1^{\mathsf T}x=\mathbf 1^{\mathsf T}Ax=\sum_j\lambda_jx_j$ for $x\ge0$, the extremes are attained at single-patch initial states. The weighted-mean identity is just $\mathbf 1^{\mathsf T}Kv=\mathcal R_0\mathbf 1^{\mathsf T}v$. When adults do not move, $V$ is diagonal on the sedentary block and $\lambda_j=\mathbf 1^{\mathsf T}(K-I)Ve_j=d_j(R_j-1)$, which gives the sign equivalence. A metapopulation can therefore be asymptotically declining ($\mathcal R_0<1$) yet transiently growing after a disturbance that leaves individuals on a source patch, or asymptotically growing yet transiently collapsing from a sink. Such transients can be made arbitrarily large, and their duration increases with the number of patches.

## Sources

- Peter D. Harrington, Mark A. Lewis, P. van den Driessche, "A framework for studying transients in marine metapopulations", arXiv:2103.09747 (2021), Section 2 (reactivity and attenuation in $\ell_1$ and $\ell_2$, lemma on column sums) and Section 5 (Lemma on $\mathcal R_0=\sum_jR_jv_j$, lemma relating $\lambda_j$ and $R_j$, Corollaries 5.3–5.5), <https://doi.org/10.48550/arXiv.2103.09747>.
