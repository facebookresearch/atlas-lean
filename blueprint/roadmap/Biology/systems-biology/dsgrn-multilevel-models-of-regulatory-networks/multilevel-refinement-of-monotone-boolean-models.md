# Multilevel refinement of monotone Boolean models

**Definitions.** A *binarization* of $X=\{0,1,\dots,m\}$ is a monotone increasing $\mu:X\to\mathbb{B}$ with $\mu(0)=0$ and $\mu(m)=1$; a binarization of $\mathcal{D}=\prod_{i=1}^N X_i$ is a coordinatewise map $\mu(d)=(\mu_1(d_1),\dots,\mu_N(d_N))$ of binarizations. A multilevel update function $g:\mathcal{D}\to\mathcal{D}$ is a *trivial multilevel refinement* of a Boolean model $f:\mathbb{B}^N\to\mathbb{B}^N$ if for each $i$ there is a binarization $\mu^i$ of $\mathcal{D}$ such that for every $d\in\mathcal{D}$:
1. $g_i(d)<d_i\Rightarrow f_i(\mu^i(d))=0$;
2. $g_i(d)>d_i\Rightarrow f_i(\mu^i(d))=1$;
3. $g_i(d)=d_i\Rightarrow f_i(\mu^i(d))=b_i$, where $b=\mu^i(d)$.

**Theorem.** Let $RN$ be a regulatory network on $V=\{1,\dots,N\}$, $f$ a monotone Boolean model for $RN$, and $(h,\theta)$ a corresponding DSGRN Boolean parameter (all components $h_i^j$ equal to the increasing form $\tilde h_i$ of $f_i$, any order parameter $\theta$). Then the multilevel update function $g$ defined by $(h,\theta)$ is a trivial multilevel refinement of $f$. The binarizations are $\mu^j_i(d_i)=\mathbf{1}[d_i\ge\theta_i(j)]$, which satisfy $f_j(\mu^j(d))=\tilde h_j(B^j(d))$ (Lemma 3.42).

So every Boolean model is reproduced, direction by direction, by a node of the DSGRN parameter graph, and the multilevel models at other nodes strictly enlarge the set of dynamics, sampling continuous switching behavior that the Boolean model only coarsely represents.

## Depends on

- [DSGRN parameter graph and multilevel update of a regulatory network](dsgrn-parameter-graph-and-multilevel-update.md)

## Expansion

At a Boolean parameter all $m_i$ components agree, so $g_i(d)=m_i\,\tilde h_i(B^i(d))$ takes only the extreme values $0$ and $m_i$. If $g_i(d)<d_i$ then $g_i(d)=0$, so $\tilde h_i(B^i(d))=0=f_i(\mu^i(d))$; symmetrically for $g_i(d)>d_i$. If $g_i(d)=d_i$ then $d_i\in\{0,m_i\}$, where every binarization takes the values $0$ and $1$ respectively, matching $f_i(\mu^i(d))$. The refinement notion is a special case of the one used for most permissive Boolean networks, so the conclusion is correspondingly stronger.

## Sources

- Breschine Cummins, Marcio Gameiro, Tomas Gedeon, Konstantin Mischaikow, "Boolean models coarsely sample continuous dynamics of regulatory networks", arXiv:2606.14925 (2026), Definitions 3.40-3.41, Lemma 3.42 and Theorem 3.43 (Section 3), <https://doi.org/10.48550/arXiv.2606.14925>
