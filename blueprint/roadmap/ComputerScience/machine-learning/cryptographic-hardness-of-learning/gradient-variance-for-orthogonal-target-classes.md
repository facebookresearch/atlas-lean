# Gradient variance bound for classes of orthogonal targets

If the target $h$ is drawn uniformly from a finite class of mutually orthogonal functions, the population gradient of the expected loss at a parameter $w$ varies with $h$ by at most $G(w)^2/|H|$ in mean square. For parities on $d$ bits, $|H|=2^d$.

Let $\mathcal{D}$ be a distribution on an input space, $w\mapsto p_w(x)$ a predictor family on an open parameter set in $\mathbb{R}^N$, $\ell$ a loss, and for a target $h$ let $F_h(w)=\mathbb{E}_{x\sim\mathcal{D}}[\ell(p_w(x),h(x))]$. For a nonempty finite class $H$ define

$$
\mathrm{Var}(H,F,w)=\mathbb{E}_h\Bigl\|\nabla F_h(w)-\mathbb{E}_{h'}\nabla F_{h'}(w)\Bigr\|^2 ,
$$

with $h,h'$ uniform on $H$.

**Theorem.** Fix $w$ and suppose

- every $h\in H$ is real valued with $\mathbb{E}_x[h(x)^2]\le1$, and $\mathbb{E}_x[h(x)h'(x)]=0$ for distinct $h,h'\in H$;
- $p_w(x)$ is differentiable in $w$ with $\mathbb{E}_x\|\partial p_w(x)/\partial w\|^2\le G(w)^2$;
- $\ell$ is the square loss $\frac12(\hat y-y)^2$, or $\ell(\hat y,y)=r(\hat yy)$ for a $1$-Lipschitz $r$ with targets in $\{\pm1\}$;
- for every $h\in H$, $F_h$ is differentiable at $w$ and its gradient may be computed under the expectation, $\nabla F_h(w)=\mathbb{E}_x[\partial_1\ell(p_w(x),h(x))\,\nabla p_w(x)]$ (for the classification loss this includes differentiability of $r$ at the relevant points).

Then $\mathrm{Var}(H,F,w)\le G(w)^2/|H|$.

For parities $H=\{x\mapsto(-1)^{\langle x,v\rangle}:v\in\{0,1\}^d\}$ under the uniform distribution on $\{0,1\}^d$, the functions are orthonormal, so the bound is $G(w)^2/2^d$.

## Expansion

For the square loss, $\nabla F_h(w)=\mathbb{E}_x[(p_w(x)-h(x))\nabla p_w(x)]$; the $h$-dependent part is $-\mathbb{E}_x[h(x)\nabla p_w(x)]$, whose $j$-th coordinate is the inner product of $h$ with $g_j=\partial_jp_w$ in $L^2(\mathcal{D})$. For an orthogonal family with $\|h\|\le1$, Bessel's inequality gives $\sum_h\langle h,g_j\rangle^2\le\|g_j\|^2$, so the variance over uniform $h$ is at most $\|g_j\|^2/|H|$; summing over $j$ gives $G(w)^2/|H|$. For the classification loss, with $\pm1$ targets $r'(\hat yh)h=\frac12(r'(\hat y)+r'(-\hat y))h+\frac12(r'(\hat y)-r'(-\hat y))$, so the $h$-dependent part of the gradient is $\mathbb{E}_x[\frac12(r'(p_w)+r'(-p_w))h\nabla p_w]$ with a multiplier bounded by $1$ (the factor $h$ must be kept). The theorem bounds only the population-gradient variance; Shalev-Shwartz, Shamir and Shammah interpret a small variance as little signal about the target in the gradient.

## Depends on

None.

## Proof depends on

None.

## Sources

- Shai Shalev-Shwartz, Ohad Shamir, Shaked Shammah, "Failures of Gradient-Based Deep Learning", ICML 2017, PMLR 70; numbers from arXiv:1703.07950v2: Section 2.1, Equation (2) and Theorem 1, with the proof in Appendix B.1.
