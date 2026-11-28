# Reduced coordinates for conserved pools

Reduced coordinates describe the concentrations of a metabolic network whose conserved-pool totals are held fixed: they are an affine parametrization of one stoichiometric class by the stoichiometric subspace.

Let $M$ (metabolites) and $R$ (reactions) be finite index sets and $N\in\mathbb{R}^{M\times R}$ a stoichiometric matrix with rank $q$, and put $p=|M|-q$. A **conserved-pool presentation** of $N$ is a pair $(B,L)$ where

- $B\in\mathbb{R}^{M\times q}$ has columns forming a basis of the stoichiometric subspace $\operatorname{im}N\subseteq\mathbb{R}^M$, and
- $L\in\mathbb{R}^{p\times M}$ has rows forming a basis of the left kernel $\{\ell\in\mathbb{R}^M:\ell^{\mathsf T}N=0\}$ (the conservation relations, or conserved pools).

The **reduced stoichiometric matrix** is the unique $N_R\in\mathbb{R}^{q\times R}$ with

$$N=B\,N_R .$$

For a reference concentration $s_{\mathrm{ref}}\in\mathbb{R}^M$ the **pool totals** are $T=Ls_{\mathrm{ref}}\in\mathbb{R}^p$ and the **reduced coordinates** are the parameters $z\in\mathbb{R}^q$ of

$$s=s_{\mathrm{ref}}+Bz .$$

The following hold for every conserved-pool presentation.

1. $N_R$ exists uniquely and has rank $q$; $LB=0$ and $\ker L=\operatorname{im}N=\operatorname{im}B$.
2. The map $z\mapsto s_{\mathrm{ref}}+Bz$ is an affine bijection from $\mathbb{R}^q$ onto the class $\{s\in\mathbb{R}^M:Ls=T\}=s_{\mathrm{ref}}+\operatorname{im}N$.
3. For every $v\in\mathbb{R}^R$, $Nv=0$ exactly when $N_Rv=0$; for every $v$, $L\,Nv=0$, so the pool totals are constant along any absolutely continuous solution of $\dot s=Nv(t)$.
4. Any two choices $B,B'$ are related by $B'=BP$, and then $N_R'=P^{-1}N_R$, for an invertible $P\in\mathbb{R}^{q\times q}$; any two choices of $L$ are related by $L'=QL$ for an invertible $Q\in\mathbb{R}^{p\times p}$, which changes $T$ to $QT$ and leaves the class unchanged.

When $q=0$ the reduced coordinates are empty and the class is the single point $s_{\mathrm{ref}}$; when $p=0$ there is no conserved pool and $B$ is invertible.

## Depends on

None.

## Proof depends on

None.

## Expansion

Every column of $N$ lies in $\operatorname{im}N=\operatorname{im}B$, and the columns of $B$ are linearly independent, so each column of $N$ has unique coordinates in that basis; these coordinates form $N_R$, and $\operatorname{rank}N_R=\operatorname{rank}(BN_R)=q$ because $B$ is injective. The left kernel of $N$ is $(\operatorname{im}N)^{\perp}$, so $\ker L=((\operatorname{im}N)^{\perp})^{\perp}=\operatorname{im}N$ and $LB=0$. Item 2 follows because $Ls=T$ means $s-s_{\mathrm{ref}}\in\ker L=\operatorname{im}B$ and $B$ is injective. Item 3: $Nv=B(N_Rv)$ vanishes exactly when $N_Rv$ does, and $LN=0$ gives $\tfrac{d}{dt}Ls=LNv=0$. Item 4: two bases of the same subspace differ by an invertible change of basis, and uniqueness of $N_R$ gives the second relation.

In Smallbone et al. the matrix playing the role of $B$ is called the link matrix and is built from independent rows of $N\varepsilon'$ rather than of $N$; the presentation here is purely stoichiometric, as in Reder's 1988 treatment that Smallbone et al. compare with. The two constructions span the same image exactly when $\operatorname{rank}(N\varepsilon')=\operatorname{rank}N$; their basis matrices may still differ by an invertible change of coordinates.

Their row-submatrix $N_r$ coincides with the coordinate matrix $N_R$ only when $B$ has identity rows at the selected indices; an arbitrary basis $B$ instead gives the coordinate matrix defined by $N=BN_R$.

## Sources

- K. Smallbone, E. Simeonidis, N. Swainston and P. Mendes, Towards a genome-scale kinetic model of cellular metabolism, *BMC Systems Biology* 4 (2010), article 6, [doi:10.1186/1752-0509-4-6](https://doi.org/10.1186/1752-0509-4-6): Methods, “Control analysis”, Equations (5)–(7) (moiety conservations, link matrix and independent metabolites) and the paragraph after Equation (11) comparing with Reder's stoichiometric link matrix.
