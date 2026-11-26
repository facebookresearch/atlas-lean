# Convex fixed-point map for mass-action steady states

**Setting.** $m$ species and $n$ complexes; $Y\in\mathbb{R}_{\ge0}^{m\times n}$ has column $y_j$ = complex $j$. The reaction graph has weighted adjacency matrix $A$ with $A_{ij}=k_{i\to j}>0$ for each reaction, $D=\operatorname{diag}(A\mathbf 1)$ and $A_k=A^{\mathsf T}-D$ (so $\mathbf 1^{\mathsf T}A_k=0$). With mass-action monomials $\psi_j(c)=\prod_i c_i^{Y_{ij}}$ and a vector $b\in\mathbb{R}^m$ of exchange fluxes across the boundary, the dynamics is

$$
\dot c=YA_k\psi(c)-b ,
$$

and a steady state is a pair $(c,v)$ with flux balance $YA_kv=b$ and mass action $v=\psi(c)$, equivalently $Y^{\mathsf T}\log c=\log v$ for $c>0$. The network is **mass conserving** if $e^{\mathsf T}YA_k=0$ for some positive vector $e$ (molecular weights); a **terminal-linkage class** is a strongly connected set of complexes, and a **single terminal-linkage network** is one whose reaction graph is a single strongly connected component.

**Construction.** Write $b=YA_k\eta$ and choose $s$ so that $\eta^+=\eta+s>0$ and $\eta^-=\eta+D^{-1}A^{\mathsf T}s>0$; then $b=YA^{\mathsf T}\eta^+-YD\eta^-$. For a parameter $\mu=(r,r_0)\in\mathbb{R}^{n+1}$ let $(v^\star(\mu),v_0^\star(\mu))$ be the unique minimizer of the strictly convex, Helmholtz-type problem

$$
\min_{(v,v_0)\ge0}\ v^{\mathsf T}D(\log v-\mathbf 1)+v_0(\log v_0-1)\quad\text{s.t.}\quad YDv+YA^{\mathsf T}\eta^+v_0=YA^{\mathsf T}r+YD\eta^-r_0 .
$$

If the minimizer is positive, the KKT conditions give a multiplier $y^\star$ with $DY^{\mathsf T}y^\star=D\log v^\star$, so $c^\star=e^{y^\star}$ satisfies mass action $\psi(c^\star)=v^\star$; and at a fixed point $\mu=(v^\star(\mu),v^\star_0(\mu))$ the constraint becomes the scaled flux balance $YA_kv^\star=v^\star_0\,b$ (consumption equals production plus exchange).

**Theorem (Akle et al., Theorem 1).** For any mass-conserving mass-action network and any rate constants $k>0$, the map $\mu\mapsto(v^\star(\mu),v^\star_0(\mu))$ has a nontrivial fixed point. In fact it maps the compact convex set

$$
\Omega_\gamma=\big\{(v,v_0)\ge0:\ e^{\mathsf T}YDv+e^{\mathsf T}YA^{\mathsf T}\eta^+v_0=\gamma\big\},\qquad\gamma>0,
$$

continuously into itself, so Brouwer's theorem gives a fixed point with prescribed total reacting mass $\gamma$ per unit time.

## Expansion

Mass conservation gives $e^{\mathsf T}b=0$, i.e. $e^{\mathsf T}YD\eta^-=e^{\mathsf T}YA^{\mathsf T}\eta^+$, and $e^{\mathsf T}YA_k=0$ gives $e^{\mathsf T}YA^{\mathsf T}=e^{\mathsf T}YD$; together they show that the weighted mass functional is preserved by the constraint, which is why $\Omega_\gamma$ is invariant. The objective is the Horn–Jackson pseudo-Helmholtz function in flux variables, whose gradient $D\log v$ makes the log-mass-action law an optimality condition. Positivity of the fixed point is the remaining issue, settled for single terminal-linkage networks.

## Sources

- S. Akle, O. Dalal, R. M. T. Fleming, M. Saunders, N. Taheri, Y. Ye, "Existence of positive steady states for mass conserving and mass-action chemical reaction networks with a single terminal-linkage class", arXiv:1105.2359 (2011). <https://doi.org/10.48550/arXiv.1105.2359>
