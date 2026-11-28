# Invariant box and equilibria of the four-dimensional HPA axis model

**Model.** Let $x_1,x_2,x_3$ be the plasma concentrations of corticotropin-releasing hormone (CRH), adrenocorticotropin (ACTH) and cortisol (CORT), and let $x_4$ be the availability of glucocorticoid receptors (GR) in the anterior pituitary. With delay kernels $h_1,h_2,h_{31},h_{32},h_{34}:[0,\infty)\to[0,\infty)$ that are bounded, piecewise continuous probability densities with finite mean, write $(h*x)(t)=\int_{-\infty}^t x(s)h(t-s)\,ds$. The distributed-delay HPA model is

$$
\begin{aligned}
\dot x_1&=k_1f_1\big(h_{31}*x_3\big)-w_1x_1,\\
\dot x_2&=k_2f_2\big(x_4\,(h_{32}*x_3)\big)\,(h_1*x_1)-w_2x_2,\\
\dot x_3&=k_3\,(h_2*x_2)-w_3x_3,\\
\dot x_4&=k_4\big(\xi+f_3\big(x_4\,(h_{34}*x_3)\big)\big)-w_4x_4,
\end{aligned}
$$

with positive constants $k_i,w_i$ and basal GR production $\xi>0$. The negative feedbacks $f_1,f_2:[0,\infty)\to(0,1]$ are smooth, bounded, strictly decreasing with $f_1(0)=f_2(0)=1$; the GR self-upregulation $f_3:[0,\infty)\to[0,1)$ is smooth, bounded, strictly increasing with $f_3(0)=0$ (for example Hill functions $f_1(u)=1-\eta u^{\alpha_1}/(c_1^{\alpha_1}+u^{\alpha_1})$, $f_3(u)=u^{\alpha_3}/(c_3^{\alpha_3}+u^{\alpha_3})$). Initial histories are bounded, continuous and nonnegative on $(-\infty,0]$.

**Invariant box.** Put $L_1=k_1/w_1$, $L_2=k_1k_2/(w_1w_2)$, $L_3=k_1k_2k_3/(w_1w_2w_3)$, $L_4=k_4/w_4$. Then both $\mathbb R^4_+$ and the compact box

$$
\Omega=[0,L_1]\times[0,L_2]\times[0,L_3]\times[0,(\xi+1)L_4]
$$

are positively invariant. In particular the receptor availability stays in $[0,1]$ whenever $(\xi+1)L_4\le 1$.

**Equilibria.** Every equilibrium lies in $\Omega$, at least one exists, and each has the form

$$
E=\Big(L_1f_1(x_0),\ \frac{w_3x_0}{k_3},\ x_0,\ \frac1{x_0}f_2^{-1}\Big(\frac{x_0}{L_3f_1(x_0)}\Big)\Big),
$$

where $x_0\in[0,L_3]$ solves

$$
L_4\Big(\xi+(f_3\circ f_2^{-1})\Big(\frac{x}{L_3f_1(x)}\Big)\Big)=\frac1x\,f_2^{-1}\Big(\frac{x}{L_3f_1(x)}\Big).
$$

Unlike the minimal three-dimensional HPA model, uniqueness is not claimed: the positive feedback $f_3$ allows several coexisting equilibria, and numerically two stable equilibria (a normal and a hypocortisolism state) can coexist.

## Expansion

Positivity follows from $\dot x_i\ge -w_ix_i$, since every production term is nonnegative. The upper bounds come from a comparison lemma: if $g'\le m_1-m_2g$ and $g(0)\le m_1/m_2$ then $g\le m_1/m_2$, because $e^{m_2t}(g-m_1/m_2)$ is nonincreasing. Using $f_1,f_2\le1$, $f_3<1$ and unit kernel mass, the bounds cascade: $x_1\le L_1$, then $x_2\le k_2L_1/w_2=L_2$, then $x_3\le L_3$, and $x_4\le(\xi+1)L_4$. At equilibrium the delays drop out, $x_1$ and $x_2$ are determined by $x_3$, and $(x_3,x_4)$ is a fixed point of $F(u,v)=\big(L_3f_1(u)f_2(uv),\,L_4(\xi+f_3(uv))\big)$, which maps the convex compact set $[0,L_3]\times[0,(\xi+1)L_4]$ into itself; Brouwer's theorem gives existence.

## Proof depends on

- [Brouwer's fixed-point theorem for products of simplices](../../../../Topology/algebraic-topology/brouwer-fixed-point-theorem/exists-fixed-point-pi.md)

## Sources

- E. Kaslik, M. Neamţu, "Stability and Hopf bifurcation analysis of a four-dimensional hypothalamic-pituitary-adrenal axis model with distributed delays", arXiv:1709.08936 (2017), Section 2 (model and kernel assumptions) and Section 3 (Positively invariant sets and equilibrium states: comparison lemma, invariance and equilibrium propositions), <https://doi.org/10.48550/arXiv.1709.08936>.
