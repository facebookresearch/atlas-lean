# Aubin–Nitsche lemma, rate form

Let $H$ and $L$ be real inner product spaces, $B$ a bounded bilinear form on $H$, $J : H \to L$ a
bounded linear map and $V_h \subseteq H$ a linear subspace. Let $\alpha > 0$ with
$\alpha \|v\|^2 \le B(v, v)$ for every $v$, and $C_{\mathrm{emb}}, C_{\mathrm{app}}, h \ge 0$ with
$\|J\| \le C_{\mathrm{emb}}$. Let $e, z \in H$ satisfy Galerkin orthogonality, $B(e, w_h) = 0$ for
$w_h \in V_h$, and the adjoint problem $B(v, z) = \langle Je, Jv\rangle$ for $v \in H$, and suppose
that some $z_h \in V_h$ has $\|z - z_h\| \le C_{\mathrm{app}}\, h\, \|z\|$. Then the weak-norm error
gains the factor $h$:

$$\alpha\, \|Je\| \le \|B\|\, C_{\mathrm{emb}}\, C_{\mathrm{app}}\, h\, \|e\| .$$
